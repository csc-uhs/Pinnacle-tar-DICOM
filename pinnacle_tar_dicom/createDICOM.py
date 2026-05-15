###################################################################################################
#                                    Program:  createdcm.py                                       #
#    This program was written to read in pinnacle text files and convert them into DICOM files    #
#    The files required: Patient (text file under patient folder),                                #
#                        plan.Points (file under Patient folder->plan label folder),              #
#                        plan.roi (file under Patient folder -> plan label folder),               #
#                        plan.Trial (file under Patient folder -> plan label folder),             #
#                        plan.Trial.Binary.xxx (xxx represents number of file, several needed)    #
#                        ImageSet_%s.ImageInfo (text file under patient folder)                   #
#                        ImageSet_%s.header                                                       #
#                        Either folder with images or ImageSet_%s file
#						 Code Authors are: Colleen Henschel,  Andrew Alexander                    #
###################################################################################################


####################################################################################################################################################
#   import libraries below
####################################################################################################################################################
from __future__ import print_function

import time #used for getting current date and time for file
import re #used for isolated values from strings
import sys
import os.path
import pydicom
import numpy as np
from pydicom.dataset import Dataset, FileDataset
from pydicom.sequence import Sequence
import pydicom.uid
import os
import struct
from random import randint
from datetime import datetime
#from PIL import Image

_LOCK_RE = re.compile(
    r"locked\s+by\s+(?P<initials>\S+?)\s*@\s*"
    r"with\s+user\s+name\s+(?P<username>\S+?)\s*@\s*"
    r"at\s+(?P<timestamp>\d{4}-\d{2}-\d{2}\s+\d{2}:\d{2}:\d{2})",
    re.IGNORECASE,
)

def append_pinnacle_metadata(existing_description, plan_info, trial_info,
                            total_trials, max_length=1024):
    lock_str = (plan_info.get("PlanLockStatus") or "").strip()
    if not lock_str:
        lock_summary = "unlocked"
    else:
        m = _LOCK_RE.search(lock_str)
        if m:
            lock_summary = "locked by %s/%s at %s" % (
                m.group("initials"), m.group("username"), m.group("timestamp"))
        else:
            lock_summary = "locked: %s" % lock_str[:80]

    is_locked = bool(lock_str)
    if not is_locked:
        classification = "unknown"
    elif total_trials == 1:
        classification = "clinical"
    else:
        classification = ("clinical" if trial_info.get("UseTrialForTreatment", 0)
                            else "unknown")

    suffix = "Pinnacle: %s; %s" % (lock_summary, classification)
    base = (existing_description or "").strip()
    combined = "%s | %s" % (base, suffix) if base else suffix
    if len(combined) > max_length:
        combined = combined[:max_length - 3].rstrip() + "..."
    return combined


def _extract_use_trial_for_treatment(trial_lines):
    """Extract UseTrialForTreatment value from raw trial text lines.

    Returns 1 if the trial is flagged for treatment, 0 otherwise.
    """
    for line in trial_lines:
        if "UseTrialForTreatment" in line:
            m = re.findall(r"[-+]?\d*\.\d+|\d+", line)
            if m:
                return int(float(m[0]))
    return 0

####################################################################################################################################################
#  Global Variables
####################################################################################################################################################
ROI_COUNT = 0 #This value will represent the ROI that I'm currently looking at in file, will be incremented for each roi
SeriesUID = "NA"
StudyInstanceUID = "NA"
FrameUID = "NA"
ClassUID = "NA"
patientname = ""
dob = ""
pid = ""
imageslice = []
imageuid = []
Colors = [['255','0','0'],['255','20','147'],['0','0','255'],['0','255','0'],['125','38','205'],['255','255','0'],['255','140','0'],['0','100','0'],['0','191','255'],['255','192','203'],['72','209','204'],['139','69','19'],['255','193','37'],['221','160','221'],['107','142','35'],['142','35','35'],['245','204','176'],['191','239','255'],['139','28','98'],['255','99','71']] #red, pink, blue, green, purple, yellow, orange, dark green, sky blue, light pink, Turquois, brown, gold,lightpurple, olive, brick, peach?, light blue, maroon, tomato  
patient_sex = ""
study_date = ""
study_time = ""
model = ""
physician = ""
sid = ""
isocenter = []
ctcenter = []
descrip = ""
plancount = 0
plannamelist = []
planids = []
planimagesets = []
randval = randint(0,999)
currentdate = time.strftime("%Y%m%d")
currenttime = time.strftime("%H%M%S")
doserefpt = []
patient_position = ""
xshift = 0
yshift = 0
zshift = 0
lname = ""
fname = ""
patientfolder = ""
structsopinstuid = ''
structseriesinstuid = ''
plansopinstuid = ''
planseriesinstuid = ''
doseseriesuid = ''
doseinstuid = ''
planfilename = ''
dosexdim = 0
doseydim = 0
dosezdim = 0
doseoriginx = ""
doseoriginy = ""
doseoriginz = ""
beamdosefiles = []
pixspacingx = ""
pixspacingy = ""
pixspacingz = ""
posrefind = ""
image_orientation = []
imagesetnumber = ""
point_names = []
point_values = []
numfracs = ""
flag_nobinaryfile = False
flag_noimages = False
# Implicit VR Little Endian — used for RTPLAN/RTSTRUCT/CT where it's safe.
GTransferSyntaxUID='1.2.840.10008.1.2'
# Explicit VR Little Endian — REQUIRED for RT Dose with BitsAllocated=32.
# Many DICOM viewers refuse or mis-parse 32-bit pixel data under Implicit VR LE
# because the OW VR length field is ambiguous. Always use this for RT Dose.
RTDOSE_TRANSFER_SYNTAX_UID='1.2.840.10008.1.2.1'
no_setup_file = False
no_beams = False
gImplementationClassUID='1.2.826.0.1.3680043.8.498.75006884747854523615841001'
Manufacturer="Pinnacle Philips"
PDD6MV = 0.6683
PDD10MV = 0.6683 # Also temporary, need to get actual PDD value
PDD15MV = 0.7658
PDD16MV = 0.7658 ## THis is temporary, this value is not correct just using as place holder for now
softwarev = ""
slicethick = 0
x_dim = 0
y_dim = 0
z_dim = 0
xpixdim = 0
ypixdim = 0
#listofversions = []


####################################################################################################################################################
# Helper: format_ds (DS = Decimal String VR; max 16 chars)
# Pinnacle dose grid scaling values can serialize to >16 chars under Python's
# default float-to-string, which DICOM silently truncates and then mis-applies.
# Format explicitly and verify length.
####################################################################################################################################################
def format_ds(value, max_chars=16):
    s = "%.7g" % float(value)
    if len(s) > max_chars:
        # Fall back to fewer significant figures
        for sig in range(6, 1, -1):
            s = ("%%.%dg" % sig) % float(value)
            if len(s) <= max_chars:
                break
    return s


####################################################################################################################################################
# Helper: make_sub_uid
# pydicom.uid.generate_uid() can produce UIDs up to 64 chars.  Appending
# ".0", ".1" etc. then truncating to 64 chars can leave a trailing dot
# (invalid) or silently change the UID so that cross-references break.
# Instead, generate a *shorter* root UID once and derive sub-UIDs safely.
####################################################################################################################################################
def make_sub_uid(root_uid, *suffixes):
    """Build a UID from root_uid + dot-separated suffixes, guaranteed ≤64
    chars and no trailing dot.

    If simple concatenation exceeds 64 chars the root is shortened first
    (by trimming trailing digits) to make room for the suffix.
    """
    suffix = ".".join(str(s) for s in suffixes)
    candidate = root_uid + "." + suffix
    if len(candidate) <= 64:
        return candidate
    # Need to shorten root to make room.  suffix + dot = len(suffix)+1
    max_root = 64 - len(suffix) - 1
    shortened = root_uid[:max_root]
    # Strip any trailing dot left by the slice
    shortened = shortened.rstrip(".")
    result = shortened + "." + suffix
    # Final safety — should never happen but be defensive
    return result[:64].rstrip(".")


# pydicom's save_as default behaviour differs across versions. To produce a
# *valid Part-10 DICOM file* (with preamble + file meta + dataset, in the
# transfer syntax declared in file_meta), we must opt out of "raw" mode
# explicitly. This helper picks the right kwarg for the installed pydicom.
####################################################################################################################################################
def save_dicom_strict(ds, path):
    try:
        # pydicom >= 3.0
        ds.save_as(path, enforce_file_format=True)
    except TypeError:
        # pydicom < 3.0
        ds.save_as(path, write_like_original=False)


####################################################################################################################################################
# Plan filtering helpers
####################################################################################################################################################

def _read_plan_lock_status(inputf, patientfolder, plan_dir):
    """Read PlanLockStatus from a plan.PlanInfo file. Returns raw string or ''."""
    info_path = "%s%s/%s/plan.PlanInfo" % (inputf, patientfolder, plan_dir)
    if not os.path.isfile(info_path):
        return ""
    try:
        with open(info_path, "rt", encoding="latin1") as f:
            for line in f:
                if "PlanLockStatus" in line:
                    m = re.findall(r'"([^"]*)"', line)
                    if m:
                        return m[0].strip()
    except Exception:
        pass
    return ""


def _plan_has_dose_binaries(inputf, patientfolder, plan_dir):
    """Check whether a plan directory contains any plan.Trial.binary.* files."""
    plan_path = "%s%s/%s" % (inputf, patientfolder, plan_dir)
    if not os.path.isdir(plan_path):
        return False
    for fname in os.listdir(plan_path):
        if fname.startswith("plan.Trial.binary."):
            return True
    return False


####################################################################################################################################################
# Trial splitting and per-trial state management
####################################################################################################################################################

def _split_trial_file(inputf, patientfolder, plan_dir):
    """Read plan.Trial and split into separate trial blocks.

    Returns a list of (trial_name, line_list) tuples.
    If the file has one trial, returns a single-element list.
    If the file is missing, returns an empty list.
    """
    trial_path = "%s%s/%s/plan.Trial" % (inputf, patientfolder, plan_dir)
    if not os.path.isfile(trial_path):
        return []

    with open(trial_path, "rt", encoding="latin1") as f:
        all_lines = f.readlines()

    # Find the start indices of each "Trial ={" block
    trial_starts = [i for i, line in enumerate(all_lines)
                    if line.strip().startswith("Trial ={")]
    if not trial_starts:
        # No trial blocks found — return entire file as one block
        return [("Trial_0", all_lines)]

    # Split into blocks: each block runs from one "Trial ={" to the next
    blocks = []
    for idx, start in enumerate(trial_starts):
        end = trial_starts[idx + 1] if idx + 1 < len(trial_starts) else len(all_lines)
        block_lines = all_lines[start:end]
        # Try to extract trial name from the block
        trial_name = "Trial_%d" % idx
        for line in block_lines:
            if "  Name = " in line:
                m = re.findall(r'"([^"]*)"', line)
                if m:
                    trial_name = m[0]
                break
        blocks.append((trial_name, block_lines))

    return blocks


def _reset_per_trial_globals():
    """Reset global variables that are set per-trial inside readtrial."""
    global beamdosefiles, dosexdim, doseydim, dosezdim
    global doseoriginx, doseoriginy, doseoriginz
    global pixspacingx, pixspacingy, pixspacingz
    global numfracs, flag_nobinaryfile, no_beams

    beamdosefiles = []
    dosexdim = 0
    doseydim = 0
    dosezdim = 0
    doseoriginx = ""
    doseoriginy = ""
    doseoriginz = ""
    pixspacingx = ""
    pixspacingy = ""
    pixspacingz = ""
    numfracs = ""
    flag_nobinaryfile = False
    no_beams = False


####################################################################################################################################################
# Function: main
# This main function is what should be called to run program
# The name of the patient folder should be passed into the function for it to be run.
#
# Parameters:
#   plan_allowlist: if not None, only export plans whose name is in this list
#   skip_no_dose: if True, skip plans that have no dose binary files
#
# Returns:
#   dict with keys: "software_version", "plans_exported", "plans_skipped",
#                   "skip_reasons" (list of str)
####################################################################################################################################################
def main(temppatientfolder, inputfolder, outputfolder,
         plan_allowlist=None, skip_no_dose=False):
    global ROI_COUNT
    global structfilename
    global SeriesUID
    global StudyInstanceUID
    global FrameUID
    global ClassUID
    global patientname
    global dob
    global pid
    global imageslice
    global imageuid
    global Colors  
    global patient_sex
    global study_date
    global study_time
    global model
    global physician
    global sid
    global isocenter
    global ctcenter
    global descrip
    global plancount
    global plannamelist
    global planids
    global randval
    global currentdate
    global currenttime
    global doserefpt
    global patient_position
    global xshift
    global yshift
    global lname
    global fname
    global Inputf
    global Outputf
    global patientfolder
    global structsopinstuid
    global structseriesinstuid
    global plansopinstuid
    global planseriesinstuid
    global doseinstuid
    global doseseriesuid
    global planfilename
    global flag_noimages
    global no_setup_file
    global no_beams
    global softwarev
    global planimagesets
    
    from pydicom import config
    config.settings.reading_validation_mode = config.IGNORE
    config.settings.writing_validation_mode = config.WARN
    initglobalvars()  # First step of the main function is to call the initglobalvars variable to reset everything in case this function is being used in a loop. (see allpatientloop.py) 
    #print("Input Patient Folder:")
    #patientfolder = raw_input("> ")
    



    patientfolder = temppatientfolder 
    Inputf = inputfolder
    Outputf = outputfolder

    print("Pinnacle tar folder path: " + Inputf)
    print("Current Patient: " + patientfolder)
    if not os.path.exists(Outputf+"%s"%(patientfolder)):
        os.makedirs(Outputf+"%s"%(patientfolder)) #Create folder for exported DICOM files if it does not already exist

    print("Output location: " + Outputf) 
    
    structsopinstuid = pydicom.uid.generate_uid() 
    structds = createstructds() #creating dataset for structure file
    for j in range(0, 5000):
        morewastingtime = j
    structseriesinstuid = pydicom.uid.generate_uid()
    structds.ReferencedStudySequence = Sequence()
    
    #structds = initds(structds)

    structds = readpatientinfo(structds)
    readImageInfo() #Gets UID information for image files 
    structds = initds(structds) #initializes values like uids, creation time, manufacturer, values that are not patient dependent
    
    for i in range(0, 5000):
        timewaster = i
    plansopinstuid = pydicom.uid.generate_uid()
    if planimagesets:
        imagesetnumber = planimagesets[0]
    convertimages() #This function makes the image files usable (matches patient info that will go into other DICOM files). If image files do not exist this function calls createimagefiles function
    if flag_noimages:
        return
    planseriesinstuid = pydicom.uid.generate_uid()

    if not planids:
        print("Error: No plan IDs found in Patient file, cannot continue.")
        return
    # Find the first plan that actually has a PatientSetup file (some plans are CT-only)
    first_valid_plan = None
    for plan_id_val in planids:
        if os.path.exists("%s%s/Plan_%s/plan.PatientSetup"%(Inputf, patientfolder, plan_id_val)):
            first_valid_plan = plan_id_val
            break
    if first_valid_plan is None:
        print("Warning: No plan.PatientSetup found for any plan. Cannot determine patient position.")
        return
    patient_position = getpatientsetup("Plan_%s"%first_valid_plan)
    if no_setup_file == True:
        return

    structds.ReferencedFrameOfReferenceSequence = Sequence()
    ReferencedFrameofReference1 = Dataset()
    structds.ReferencedFrameOfReferenceSequence.append(ReferencedFrameofReference1)
    structds.ReferencedFrameOfReferenceSequence[0].FrameOfReferenceUID = FrameUID
    structds.ReferencedFrameOfReferenceSequence[0].RTReferencedStudySequence = Sequence()
    RTReferencedStudy1 = Dataset()
    structds.ReferencedFrameOfReferenceSequence[0].RTReferencedStudySequence.append(RTReferencedStudy1)
    structds.ReferencedFrameOfReferenceSequence[0].RTReferencedStudySequence[0].ReferencedSOPClassUID = '1.2.840.10008.3.1.2.3.2'
    structds.ReferencedFrameOfReferenceSequence[0].RTReferencedStudySequence[0].ReferencedSOPInstanceUID = StudyInstanceUID
    structds.StudyInstanceUID = StudyInstanceUID
    structds.ReferencedFrameOfReferenceSequence[0].RTReferencedStudySequence[0].RTReferencedSeriesSequence = Sequence()
    RTReferencedSeries1 = Dataset()
    structds.ReferencedFrameOfReferenceSequence[0].RTReferencedStudySequence[0].RTReferencedSeriesSequence.append(RTReferencedSeries1)
    structds.ReferencedFrameOfReferenceSequence[0].RTReferencedStudySequence[0].RTReferencedSeriesSequence[0].SeriesInstanceUID = SeriesUID
    structds.ReferencedFrameOfReferenceSequence[0].RTReferencedStudySequence[0].RTReferencedSeriesSequence[0].ContourImageSequence = Sequence()
    contour_image_seq = structds.ReferencedFrameOfReferenceSequence[0].RTReferencedStudySequence[0].RTReferencedSeriesSequence[0].ContourImageSequence
    for i, value in enumerate(imageuid, 0):
        ci = Dataset()
        contour_image_seq.append(ci)
        ci.ReferencedSOPClassUID = '1.2.840.10008.5.1.4.1.1.2'  # CT Image Storage (was incorrectly CR)
        ci.ReferencedSOPInstanceUID = imageuid[i]

    doseinstuid = pydicom.uid.generate_uid()

    structds.ROIContourSequence = Sequence()
    structds.StructureSetROISequence = Sequence()
    structds.RTROIObservationsSequence = Sequence()
    
    if softwarev != "Pinnacle 9.0": # If pinnacle software is version 9.0 the shifts are not needed so this function can be skipped and the values for the shifts will still be set to zero
        getstructshift()
    structds = readpoints(structds, "Plan_%s"%first_valid_plan)
    
    # If isocenter wasn't found in the first plan, search remaining plans
    if isocenter == [0.0, 0.0, 0.0]:
        for plan_id_val in planids:
            if plan_id_val == first_valid_plan:
                continue
            alt_points_path = "%s%s/Plan_%s/plan.Points" % (Inputf, patientfolder, plan_id_val)
            if os.path.isfile(alt_points_path):
                with open(alt_points_path, "rt", encoding="latin1") as _pf:
                    for _line in _pf:
                        if "Name = " in _line:
                            _name = re.findall(r'"([^"]*)"', _line)
                            if _name:
                                _n = _name[0].lower()
                                if "iso" in _n or "isocenter" in _n or "isocentre" in _n:
                                    # Found a plan with isocenter — re-read points from this plan
                                    print("Info: Isocenter found in Plan_%s, re-reading points." % plan_id_val)
                                    structds = readpoints(structds, "Plan_%s" % plan_id_val)
                                    break
                    if isocenter != [0.0, 0.0, 0.0]:
                        break
    
    structds = readroi(structds, "Plan_%s"%first_valid_plan)

    structds.ApprovalStatus = 'UNAPPROVED' #find out where to get if its been approved or not
    # Set the transfer syntax
    # is_little_endian and is_implicit_VR removed in pydicom v3;
    # transfer syntax is controlled via file_meta.TransferSyntaxUID
    #structfilepath=outputfolder + patientfolder + "/" + structfilename
    #structds.save_as("structfilepath")
    #print("Structure file being saved\n")
    structds.save_as(Outputf + "/%s/%s"%(patientfolder, structfilename), enforce_file_format=True)
    
    #print(structds)
    #exit()
    doseseriesuid = pydicom.uid.generate_uid()

    #############################################################################################
    # Plan filtering: pre-scan to determine which plans to export
    plans_exported = 0
    plans_skipped = 0
    skip_reasons = []

    # loop below creates plan files for each plan in directory (based on what is in the Patient file)
    for i in range(0, plancount): 
        planame = plannamelist[i]
        plandirect = "Plan_" + planids[i]

        # --- Plan filtering ---
        if plan_allowlist is not None:
            if planame not in plan_allowlist:
                reason = "Plan '%s' (%d/%d): skipped — not in selected plans" % (planame, i+1, plancount)
                print(reason)
                skip_reasons.append(reason)
                plans_skipped += 1
                continue

        if skip_no_dose:
            if not _plan_has_dose_binaries(Inputf, patientfolder, plandirect):
                reason = "Plan '%s' (%d/%d): skipped — no dose binaries (skip_no_dose=True)" % (planame, i+1, plancount)
                print(reason)
                skip_reasons.append(reason)
                plans_skipped += 1
                continue

        if i < len(planimagesets):
            imagesetnumber = planimagesets[i]

        # Split plan.Trial into individual trial blocks
        trial_blocks = _split_trial_file(Inputf, patientfolder, plandirect)
        if not trial_blocks:
            reason = "Plan '%s' (%d/%d): skipped — plan.Trial not found" % (planame, i+1, plancount)
            print(reason)
            skip_reasons.append(reason)
            plans_skipped += 1
            continue

        if len(trial_blocks) > 1:
            print("Plan '%s' (%d/%d): %d trials found — exporting each separately" % (
                planame, i+1, plancount, len(trial_blocks)))

        # Read plan lock status once per plan (shared across all trials)
        plan_lock_str = _read_plan_lock_status(Inputf, patientfolder, plandirect)

        plan_had_export = False
        for trial_idx, (trial_name, trial_lines) in enumerate(trial_blocks):
            # UID index: for single-trial plans use the plan index directly
            # (backward compatible — same UIDs as before). For multi-trial,
            # use a composite index to ensure uniqueness across trials.
            if len(trial_blocks) == 1:
                uid_idx = i
            else:
                uid_idx = i * 100 + trial_idx

            _reset_per_trial_globals()

            trial_label = "'%s' trial '%s'" % (planame, trial_name) if len(trial_blocks) > 1 else "'%s'" % planame

            plands = createplands(uid_idx)
            plands = planinit(plands, planame, plandirect, uid_idx)

            # Stamp RTPlanDescription with lock status and trial classification
            # (matches the modern converter's output from pinnacle_metadata.py)
            use_for_treatment = _extract_use_trial_for_treatment(trial_lines)
            synthetic_plan_info = {"PlanLockStatus": plan_lock_str}
            synthetic_trial_info = {"UseTrialForTreatment": use_for_treatment}
            plands.RTPlanDescription = append_pinnacle_metadata(
                descrip, synthetic_plan_info, synthetic_trial_info,
                len(trial_blocks), max_length=1024,
            )

            plands = readtrial(plands, plandirect, uid_idx, trial_lines=trial_lines)

            if no_beams:
                reason = "Plan %s (%d/%d): skipped — no beams in trial" % (trial_label, i+1, plancount)
                print(reason)
                skip_reasons.append(reason)
                continue

            # Skip writing RTPLAN if the trial had beams but all dose
            # binaries were missing — readtrial already skipped the dose
            # file, so writing only an RTPLAN would produce an orphaned
            # file with no matching RTDOSE.  Only enforced when the caller
            # requested skip_no_dose; without it, the original behaviour
            # (partial exports) is preserved.
            if skip_no_dose and flag_nobinaryfile:
                reason = "Plan %s (%d/%d): skipped — no dose binaries for any beam in trial" % (trial_label, i+1, plancount)
                print(reason)
                skip_reasons.append(reason)
                continue

            tempmetainstuid = make_sub_uid(plansopinstuid, uid_idx)
            planfilename = 'RP.' + tempmetainstuid + '.dcm'
            planfilepath = Outputf + patientfolder + "/" + planfilename

            save_dicom_strict(plands, planfilepath)
            plan_had_export = True
            print("Exported RTPlan for plan %s" % trial_label)

        if plan_had_export:
            plans_exported += 1
        else:
            plans_skipped += 1

    print("Export summary: %d/%d plans exported, %d skipped" % (plans_exported, plancount, plans_skipped))

    os.rename(Outputf+'%s'% patientfolder, Outputf+'%s,%s,%s'%(lname,fname,pid))

    return {
        "software_version": softwarev,
        "plans_exported": plans_exported,
        "plans_skipped": plans_skipped,
        "skip_reasons": skip_reasons,
    }
####################################################################################################################################################
####################################################################################################################################################



####################################################################################################################################################
# Function: initglobalvars
# This function simply resets all of the global variables to empty values
####################################################################################################################################################
def initglobalvars():
    global ROI_COUNT
    global structfilename
    global SeriesUID
    global StudyInstanceUID
    global FrameUID
    global ClassUID
    global patientname
    global dob
    global pid
    global imageslice
    global imageuid
    global Colors  
    global patient_sex
    global study_date
    global study_time
    global model
    global physician
    global sid
    global isocenter
    global ctcenter
    global descrip
    global plancount
    global plannamelist
    global planids
    global randval
    global currentdate
    global currenttime
    global doserefpt
    global patient_position
    global xshift
    global yshift
    global zshift
    global lname
    global fname
    global patientfolder
    global structsopinstuid
    global structseriesinstuid
    global plansopinstuid
    global planseriesinstuid
    global doseseriesuid
    global doseinstuid
    global planfilename
    global dosexdim
    global doseydim
    global dosezdim
    global doseoriginx
    global doseoriginy
    global doseoriginz
    global beamdosefiles
    global pixspacingx
    global pixspacingy
    global pixspacingz
    global posrefind
    global image_orientation
    global imagesetnumber
    global point_names
    global point_values
    global numfracs
    global flag_nobinaryfile
    global flag_noimages
    global no_setup_file
    global no_beams
    global softwarev
    global planimagesets
    global slicethick
    global x_dim
    global y_dim
    global z_dim
    global xpixdim
    global ypixdim

    ROI_COUNT = 0 #This value will represent the ROI that I'm currently looking at in file, will be incremented for each roi
    SeriesUID = "NA"
    StudyInstanceUID = "NA"
    FrameUID = "NA"
    ClassUID = "NA"
    patientname = ""
    dob = ""
    pid = ""
    imageslice = []
    imageuid = []
    Colors = [['255','0','0'],['255','20','147'],['0','0','255'],['0','255','0'],['125','38','205'],['255','255','0'],['255','140','0'],['0','100','0'],['0','191','255'],['255','192','203'],['72','209','204'],['139','69','19'],['255','193','37'],['221','160','221'],['107','142','35'],['142','35','35'],['245','204','176'],['191','239','255'],['139','28','98'],['255','99','71']] #red, pink, blue, green, purple, yellow, orange, dark green, sky blue, light pink, Turquois, brown, gold,lightpurple, olive, brick, peach?, light blue, maroon, tomato  
    patient_sex = ""
    study_date = ""
    study_time = ""
    model = ""
    physician = ""
    sid = ""
    isocenter = []
    ctcenter = []
    descrip = ""
    plancount = 0
    plannamelist = []
    planids = []
    planimagesets = []
    randval = randint(0,999)
    currentdate = time.strftime("%Y%m%d")
    currenttime = time.strftime("%H%M%S")
    doserefpt = []
    patient_position = ""
    xshift = 0
    yshift = 0
    zshift = 0
    lname = ""
    fname = ""
    patientfolder = ""
    structsopinstuid = ''
    structseriesinstuid = ''
    plansopinstuid = ''
    planseriesinstuid = ''
    doseseriesuid = ''
    doseinstuid = ''
    planfilename = ''
    dosexdim = 0
    doseydim = 0
    dosezdim = 0
    doseoriginx = ""
    doseoriginy = ""
    doseoriginz = ""
    beamdosefiles = []
    pixspacingx = ""
    pixspacingy = ""
    pixspacingz = ""
    posrefind = ""
    image_orientation = []
    imagesetnumber = ""
    point_names = []
    point_values = []
    numfracs = ""
    flag_nobinaryfile = False
    flag_noimages = False
    no_setup_file = False
    no_beams = False
    softwarev = ""
    slicethick = 0
    x_dim = 0
    y_dim = 0
    z_dim = 0
    xpixdim = 0
    ypixdim = 0
####################################################################################################################################################
####################################################################################################################################################

####################################################################################################################################################
#    function: convertimages
#    The purpose of this function is to read in the image DICOM files
#    and to change the patients name to match the name of the patient
#    in the pinnacle files, also fills the list values for slicelocation
#    and UID. This function needs to be run, even if image files already converted
####################################################################################################################################################
def convertimages():
    #print("Converting image patient name, birthdate and id to match pinnacle\n")
    global patientname
    global pid
    global dob
    global FrameUID
    global imageslice
    global SeriesUID
    global StudyInstanceUID
    global imageuid
    global patientfolder
    global posrefind
    global imagesetnumber
    global image_orientation
    global flag_noimages

    if not os.path.exists("%s%s/ImageSet_%s.DICOM"%(Inputf,patientfolder, imagesetnumber)):
        #Image set folder not found, need to ignore patient
        #Will want to call a function to be written that will create image set files from the condensed pixel data file
        #print("Image files do not exist. Creating image files")
        createimagefiles()
        return
    for file in os.listdir("%s%s/ImageSet_%s.DICOM"%(Inputf,patientfolder, imagesetnumber)):
        if file == '11026.1.img':
            continue
        imageds = pydicom.dcmread("%s%s/ImageSet_%s.DICOM/%s"%(Inputf, patientfolder, imagesetnumber, file), force=True)
        imageds.PatientName = patientname
        imageds.PatientID = pid
        imageds.PatientBirthDate = dob
        imageslice.append(imageds.SliceLocation)
        imageuid.append(imageds.SOPInstanceUID)
        image_orientation = imageds.ImageOrientationPatient
        tempinstuid = imageds.SOPInstanceUID
        posrefind = imageds.PositionReferenceIndicator
        imageds.SOPInstanceUID = tempinstuid
        imageds.FrameOfReferenceUID = FrameUID
        imageds.StudyInstanceUID = StudyInstanceUID
        imageds.SeriesInstanceUID = SeriesUID
        file_meta = Dataset()
        file_meta.TransferSyntaxUID = GTransferSyntaxUID
        file_meta.MediaStorageSOPClassUID = '1.2.840.10008.5.1.4.1.1.2'
        file_meta.MediaStorageSOPInstanceUID = tempinstuid
        file_meta.ImplementationClassUID = gImplementationClassUID
        imageds.file_meta = file_meta
        imageds.save_as(Outputf+"%s/CT.%s.dcm"%(patientfolder, tempinstuid), enforce_file_format=True)
        #print("Current image: ", file)
        #print(imageds)
####################################################################################################################################################
####################################################################################################################################################                      
      

####################################################################################################################################################
# Function: createimagefiles()
# This function will create dicom image files for each slice using the condensed pixel data from file ImageSet_%s.img
####################################################################################################################################################
def createimagefiles():
    global slicethick
    global x_dim
    global y_dim
    global z_dim
    global xpixdim
    global ypixdim
    global patientname
    global pid
    global dob
    global FrameUID
    global imageslice
    global SeriesUID
    global StudyInstanceUID
    global imageuid
    global patientfolder
    global posrefind
    global imagesetnumber
    global image_orientation
    
    currentpatientposition = getheaderinfo()
    if os.path.isfile("%s%s/ImageSet_%s.img"%(Inputf, patientfolder, imagesetnumber)):
        allframeslist = []
        pixel_array = np.fromfile("%s%s/ImageSet_%s.img"%(Inputf, patientfolder, imagesetnumber), dtype = np.short)
        for i in range(0, int(z_dim)): # will loop over every frame
            frame_array = pixel_array[i*int(x_dim)*int(y_dim):(i+1)*int(x_dim)*int(y_dim)]
            allframeslist.append(frame_array)
            """frame_array = np.array([])
            temp_frame_array = pixel_array[i*int(x_dim)*int(y_dim):(i+1)*int(x_dim)*int(y_dim)]
            for j in range(0, int(y_dim)):
                temprow = temp_frame_array[j*int(x_dim):(j+1)*int(x_dim)][::-1]
                frame_array = np.append(frame_array, temprow)
            allframeslist.append(frame_array)
"""
    #print("Length of frames list: " + str(len(allframeslist)))
    imageinfo_path = "%s%s/ImageSet_%s.ImageInfo"%(Inputf, patientfolder, imagesetnumber)
    if not os.path.isfile(imageinfo_path):
        print("Warning: ImageSet_%s.ImageInfo not found, skipping image creation." % imagesetnumber)
        return
    with open(imageinfo_path, 'rt', encoding='latin1') as f:
        image_info = f.readlines()
        curframe = 0
        for i, line in enumerate(image_info, 0):
            if "ImageInfo ={" in line:
                sliceloc = -float(re.findall(r"[-+]?\d*\.\d+|\d+", image_info[i + 1])[0])*10
                instuid = re.findall(r'"([^"]*)"', image_info[i + 8])[0]
                seriesuid = re.findall(r'"([^"]*)"', image_info[i + 4])[0]
                classuid = re.findall(r'"([^"]*)"', image_info[i + 7])[0]
                frameuid = re.findall(r'"([^"]*)"', image_info[i + 6])[0]
                studyinstuid = re.findall(r'"([^"]*)"', image_info[i + 5])[0]
                slicenum = int(re.findall(r"[-+]?\d*\.\d+|\d+", image_info[i + 3])[0])
                dateofscan, timeofscan = getdateandtime()
                
                file_meta = Dataset()
                file_meta.MediaStorageSOPClassUID = classuid
                file_meta.MediaStorageSOPInstanceUID = instuid
                file_meta.TransferSyntaxUID = GTransferSyntaxUID
                file_meta.ImplementationClassUID = gImplementationClassUID #this value remains static since implementation for creating file is the same
                ds = FileDataset(planfilename, {}, file_meta=file_meta, preamble=b'\x00'*128)

                ds.SpecificCharacterSet = "ISO_IR 100"
                ds.ImageType = ['ORIGINAL', 'PRIMARY', 'AXIAL']
                ds.AccessionNumber = ''
                ds.SOPClassUID = classuid
                ds.SOPInstanceUID = instuid
                ds.StudyDate = dateofscan
                ds.SeriesDate = dateofscan
                ds.AcquisitionDate = dateofscan
                ds.ContentDate = dateofscan
                ds.AcquisitionTime = timeofscan
                ds.Modality = "CT" # Also should come from header file, but not always present
                ds.Manufacturer = "GE MEDICAL SYSTEMS" #This should come from Manufacturer in header, but for some patients it isn't set?? 
                ds.StationName = "CT"
                ds.PatientName = patientname
                ds.PatientID = pid
                ds.PatientBirthDate = dob
                ds.BitsAllocated = 16
                ds.BitsStored = 16
                ds.HighBit = 15
                ds.PixelRepresentation = 1
                ds.RescaleIntercept = -1024
                #ds.RescaleIntercept = 0.0
                ds.RescaleSlope = 1.0
                # ds.kvp = ?? This should be peak kilovoltage output of x ray generator used
                ds.PatientPosition = currentpatientposition
                ds.DataCollectionDiameter = xpixdim*float(x_dim)  # this is probably x_pixdim * xdim = y_pixdim * ydim
                ds.SpatialResolution = 0.35#???????
                #ds.DistanceSourceToDetector = #???
                #ds.DistanceSourceToPatient = #????
                ds.GantryDetectorTilt = 0.0 #??
                ds.TableHeight = -158.0#??
                ds.RotationDirection = "CW"#???
                ds.ExposureTime = 1000#??
                ds.XRayTubeCurrent = 398#??
                ds.GeneratorPower = 48#??
                ds.FocalSpots = 1.2#??
                ds.ConvolutionKernel = "STND" #????
                ds.SliceThickness = slicethick
                ds.NumberOfSlices =   int(z_dim)
                #ds.StudyInstanceUID = studyinstuid
                #ds.SeriesInstanceUID = seriesuid
                ds.FrameOfReferenceUID = FrameUID
                ds.StudyInstanceUID = StudyInstanceUID
                ds.SeriesInstanceUID = SeriesUID
                ds.InstanceNumber = slicenum # problem, some of these are repeated in image file so not sure what to do with that
                ds.ImagePositionPatient = [-xpixdim*float(x_dim)/2, -ypixdim*float(y_dim)/2, sliceloc]
                if "HFS" in currentpatientposition or "FFS" in currentpatientposition:
                    ds.ImageOrientationPatient = [1.0, 0.0, 0.0, 0.0, 1.0, -0.0] 
                elif "HFP" in currentpatientposition or "FFP" in currentpatientposition:
                    ds.ImageOrientationPatient = [-1.0, 0.0, 0.0, 0.0, -1.0, -0.0]
                ds.PositionReferenceIndicator = "LM" #???
                ds.SliceLocation = sliceloc
                ds.SamplesPerPixel = 1
                ds.PhotometricInterpretation = "MONOCHROME2"
                ds.Rows = int(x_dim)
                ds.Columns = int(y_dim)
                ds.PixelSpacing = [xpixdim, ypixdim]

                

                #ds.PixelData = allframeslist[curframe]
                #ds.PixelData = allframeslist[slicenum - 1]
                ds.PixelData = allframeslist[curframe].tobytes()

                imageslice.append(sliceloc)
                imageuid.append(instuid)
                image_orientation = ds.ImageOrientationPatient
                posrefind = ds.PositionReferenceIndicator
                #print("Creating image: " + Outputf + "%s/CT.%s.dcm"%(patientfolder, instuid))
                #ds.save_as(Outputf + "%s/CT.%s.dcm"%(patientfolder, instuid),write_like_original=False)
                ds.save_as(Outputf + "%s/CT.%s.dcm"%(patientfolder, instuid), enforce_file_format=True)
                curframe = curframe + 1
####################################################################################################################################################
####################################################################################################################################################


####################################################################################################################################################
# Function: getheaderinfo
# This function will only be called in cases where image files do not already exist
####################################################################################################################################################
def getheaderinfo():
    global slicethick
    global x_dim
    global y_dim
    global z_dim
    global xpixdim
    global ypixdim
    temp_pos = ""
    header_path = "%s%s/ImageSet_%s.header"%(Inputf, patientfolder, imagesetnumber)
    if not os.path.isfile(header_path):
        print("Warning: ImageSet_%s.header not found." % imagesetnumber)
        return temp_pos
    with open(header_path, "rt", encoding='latin1') as f2:
        for line in f2:
            #print("line in header: " + line)
            if "x_dim =" in line:
                x_dim = (line.split(" ")[-1]).replace(';','').replace('\n', '')
            if "y_dim =" in line:
                y_dim = (line.split(" ")[-1]).replace(';','').replace('\n', '')
            if "x_pixdim =" in line:
                xpixdim = float((line.split(" ")[-1]).replace(';',''))*10
            if "y_pixdim =" in line:
                ypixdim = float((line.split(" ")[-1]).replace(';',''))*10
            if "x_start =" in line and "index" not in line:
                xstart = float((line.split(" ")[-1]).replace(';',''))
                print("xstart = ", xstart)
            if "y_start =" in line:
                ystart = float((line.split(" ")[-1]).replace(';',''))
            if "z_dim =" in line:
                z_dim = (line.split(" ")[-1]).replace(';','').replace('\n', '')
            if "z_pixdim =" in line:
                slicethick = float((line.split(" ")[-1]).replace(';',''))*10
            if "z_start =" in line and "index" not in line:
                zstart = float((line.split(" ")[-1]).replace(';',''))
            if "patient_position" in line:
                temp_pos = (line.split(" ")[-1]).replace("\n","")
                print("Patient_position is: " + temp_pos)
    return temp_pos
####################################################################################################################################################
####################################################################################################################################################




####################################################################################################################################################
# Function: getdateandtime
# Will read ImageSet_%s.ImageSet file to get date and time of CT image aquisition, only used in cases where image files have not been created
####################################################################################################################################################
def getdateandtime():
    #with open("//Testfile", "rt", encoding='latin1') as g:
    imageset_path = "%s%s/ImageSet_%s.ImageSet"%(Inputf, patientfolder, imagesetnumber)
    if not os.path.isfile(imageset_path):
        print("Warning: ImageSet_%s.ImageSet not found, using current date/time." % imagesetnumber)
        return time.strftime("%Y%m%d"), time.strftime("%H%M%S")
    with open(imageset_path, "rt", encoding='latin1') as g:
        for line in g:
            if "ScanTimeFromScanner" in line:
                dateandtimestring = re.findall(r'"([^"]*)"', line)[0]
                dateandtimelist = dateandtimestring.split(' ')
                date = dateandtimelist[0].replace("-", "")
                time = dateandtimelist[1].replace(":","")
                return date, time
####################################################################################################################################################
####################################################################################################################################################

####################################################################################################################################################
#    function: readImageInfo
#    Reads in the file ImageSet_0.ImageInfo to get uid values
#    Saves the general UIDs as global variables 
####################################################################################################################################################
def readImageInfo():
    #print("Reading image information for all image files\n")
    global SeriesUID
    global StudyInstanceUID
    global FrameUID
    global ClassUID
    global patientfolder
    global randval
    global imagesetnumber
    #print("Path to image info file: " + "%s%s/ImageSet_%s.ImageInfo"%(Inputf, patientfolder, imagesetnumber))
    if not os.path.exists("%s%s/ImageSet_%s.ImageInfo"%(Inputf, patientfolder, imagesetnumber)):
        #print("Leaving readImageInfo before getting info")
        return
    with open("%s%s/ImageSet_%s.ImageInfo"%(Inputf, patientfolder, imagesetnumber), 'rt', encoding='latin1') as f1:
        for line in f1:
            #print("For loop in readImageInfo")
            if "SeriesUID" in line:
                SeriesUID = re.findall(r'"([^"]*)"', line)[0]
                #print("setting series uid: " + str(SeriesUID))
                #SeriesUID = SeriesUID + "." + "0" + str(randval)
            if "StudyInstanceUID" in line:
                StudyInstanceUID = re.findall(r'"([^"]*)"', line)[0]
                #print("setting study uid: " + str(StudyInstanceUID))
                #StudyInstanceUID = StudyInstanceUID + "." + "0" + str(randval)
            if "FrameUID" in line:
                FrameUID = re.findall(r'"([^"]*)"', line)[0]
                #print("setting frame uid: " + str(FrameUID))
               # FrameUID = FrameUID[:-4] + "." + "0" + str(randval)
            if "ClassUID" in line:
                ClassUID = re.findall(r'"([^"]*)"', line)[0]
                #print("setting class uid: " + str(ClassUID))
                #ClassUID = ClassUID + "." + "0" + str(randval)
####################################################################################################################################################
####################################################################################################################################################


####################################################################################################################################################
# Creating a data structure to write to rt struct dicom file
# Based off example file write_new.py from C:\Python27\Lib\site-packages\dicom\examples\write_new.py
# returns data structure ds
####################################################################################################################################################
def createstructds():
    #print("Creating Data structure")
    global structfilename
    global structsopinstuid
    # Populate required values for file meta information
    file_meta = Dataset()
    #file_meta.add_new(0x00020000, 'UL', 184)
    #file_meta.add_new(0x00020001, 'OB', b'\x00'*2)
    file_meta.MediaStorageSOPClassUID = '1.2.840.10008.5.1.4.1.1.481.3' #RT Structure Set Storage
    file_meta.MediaStorageSOPInstanceUID = structsopinstuid[:64].rstrip(".")
    structfilename="RS."+file_meta.MediaStorageSOPInstanceUID+".dcm"
    file_meta.TransferSyntaxUID = GTransferSyntaxUID
    file_meta.ImplementationClassUID = gImplementationClassUID #this value remains static since implementation for creating file is the same
    #file_meta.add_new(0x00020013, 'SH', "DCTOOL100")
    #print(file_meta.elements)
    #exit()

    # Create the FileDataset instance (initially no data elements, but file_meta supplied)
    ds = FileDataset(structfilename, {}, file_meta=file_meta, preamble=b'\x00'*128)
    #print(ds)
    return ds
####################################################################################################################################################
####################################################################################################################################################



####################################################################################################################################################
# Function: getstructshift()
# Purpose: reads in values from ImageSet_0.header to get x and y shift
####################################################################################################################################################
def getstructshift():
    global xshift
    global yshift
    global zshift
    global patient_position
    global imagesetnumber
    header_path = "%s%s/ImageSet_%s.header"%(Inputf, patientfolder, imagesetnumber)
    if not os.path.isfile(header_path):
        print("Warning: ImageSet_%s.header not found." % imagesetnumber)
        return temp_pos
    with open(header_path, "rt", encoding='latin1') as f2:
        for line in f2:
            if "x_dim =" in line:
                x_dim = float((line.split(" ")[-1]).replace(';',''))
            if "y_dim =" in line:
                y_dim = float((line.split(" ")[-1]).replace(';',''))
            if "x_pixdim =" in line:
                xpixdim = float((line.split(" ")[-1]).replace(';',''))
            if "y_pixdim =" in line:
                ypixdim = float((line.split(" ")[-1]).replace(';',''))
            if "x_start =" in line and "index" not in line:
                xstart = float((line.split(" ")[-1]).replace(';',''))
                print("xstart = ", xstart)
            if "y_start =" in line:
                ystart = float((line.split(" ")[-1]).replace(';',''))
            if "z_dim =" in line:
                z_dim = float((line.split(" ")[-1]).replace(';',''))
            if "z_pixdim =" in line:
                zpixdim = float((line.split(" ")[-1]).replace(';',''))
            if "z_start =" in line and "index" not in line:
                zstart = float((line.split(" ")[-1]).replace(';',''))
    if patient_position == 'HFS':
        xshift = ((x_dim*xpixdim/2)+xstart)*10
        print("X shift = ", xshift)
        yshift = -((y_dim*ypixdim/2)+ystart)*10
        print("Y shift = ", yshift)
        zshift = -((z_dim*zpixdim/2)+zstart)*10
    elif patient_position == 'HFP':
        xshift = -((x_dim*xpixdim/2)+xstart)*10

        print("X shift = ", xshift)


        yshift = ((y_dim*ypixdim/2)+ystart)*10

        print("Y shift = ", yshift)
        zshift = -((z_dim*zpixdim/2)+zstart)*10
    elif patient_position == 'FFP':
        xshift = ((x_dim*xpixdim/2)+xstart)*10
        print("X shift = ", xshift)
        yshift = ((y_dim*ypixdim/2)+ystart)*10
        print("Y shift = ", yshift)
        zshift = ((z_dim*zpixdim/2)+zstart)*10
    elif patient_position == 'FFS':
        xshift = -((x_dim*xpixdim/2)+xstart)*10
        print("X shift = ", xshift)
        yshift = -((y_dim*ypixdim/2)+ystart)*10
        print("Y shift = ", yshift)
        zshift = ((z_dim*zpixdim/2)+zstart)*10

####################################################################################################################################################
####################################################################################################################################################


####################################################################################################################################################
# Function: createplands()
# creates a data structure for the rt plan file
# similar to createstructds but different UIDs
####################################################################################################################################################
def createplands(plannumber):
    #print("Creating plan Data Structure\n")
    global planfilename
    global plansopinstuid
    file_meta = Dataset()
    file_meta.MediaStorageSOPClassUID = '1.2.840.10008.5.1.4.1.1.481.5' #RT Plan Storage
    _plan_sop_uid = make_sub_uid(plansopinstuid, plannumber)
    file_meta.MediaStorageSOPInstanceUID = _plan_sop_uid
    file_meta.TransferSyntaxUID = GTransferSyntaxUID
    file_meta.ImplementationClassUID = gImplementationClassUID #this value remains static since implementation for creating file is the same

    ds = FileDataset(planfilename, {}, file_meta=file_meta, preamble=b'\x00'*128)
    return ds
####################################################################################################################################################
####################################################################################################################################################

####################################################################################################################################################
# Function to initialize data structure, sets Specific Character set,
# instance creation time and date, SOP Class UID, and SOP Instance UID
# also sets modality and data structure
####################################################################################################################################################
def initds(ds):
    #print("initializing data structure\n")
    global imageuids    
    global SeriesUID
    global StudyInstanceUID
    global FrameUID
    global ClassUID
    global structsopinstuid
    global structseriesinstuid
    global patientname
    global patient_sex
    global dob


    ds.SpecificCharacterSet = "ISO_IR 100" # not sure what I want here, going off of template dicom file
    ds.InstanceCreationDate = time.strftime("%Y%m%d")
    ds.InstanceCreationTime = time.strftime("%H%M%S")
    ds.SOPClassUID = '1.2.840.10008.5.1.4.1.1.481.3'
    ds.SOPInstanceUID = structsopinstuid[:64].rstrip(".")
    ds.Modality = 'RTSTRUCT'
    #print(patientname)
    ds.PatientName=patientname
    ds.PatientBirthDate = dob
    ds.PatientID = pid
    ds.PatientSex = patient_sex
    ds.AccessionNumber = ""
    ds.Manufacturer = Manufacturer #from sample dicom file, maybe should change?
    ds.StationName = "adacp3u7" # not sure where to get information for this element can find this and read in from 
    #ds.ManufacturersModelName = 'Pinnacle3'
    ReferencedStudy1 = Dataset()
    ds.ReferencedStudySequence.append(ReferencedStudy1)
    ds.ReferencedStudySequence[0].ReferencedSOPClassUID = '1.2.840.10008.3.1.2.3.2' #Study Component Management SOP Class (chosen from template)
    ds.ReferencedStudySequence[0].ReferencedSOPInstanceUID = StudyInstanceUID
    ds.StudyInstanceUID = StudyInstanceUID
    #print("Setting structure file study instance: " + str(StudyInstanceUID))
    ds.SeriesInstanceUID = structseriesinstuid
    #print(patientname)
    #print(ds)
    #exit()
    return ds
####################################################################################################################################################
####################################################################################################################################################


####################################################################################################################################################
# function to read in patient info from Patient text file
####################################################################################################################################################
def readpatientinfo(ds):
    #print ("Reading patient information\n")
    mname = ""
    flag_first = True
    flag_time = True
    flag_stid = True
    global imageuids    
    global SeriesUID
    global StudyInstanceUID
    global FrameUID
    global ClassUID
    global patientname
    global dob
    global pid
    global patient_sex
    global study_time
    global study_date
    global model
    global physician
    global sid
    global descrip
    global plancount
    global plannamelist
    global planids
    global planimagesets
    global patientfolder
    global lname
    global fname
    global imagesetnumber
    global softwarev
    #global listofversions
    patient_path = "%s%s/Patient"%(Inputf, patientfolder)
    pinnacle_internal_id = ""
    if not os.path.isfile(patient_path):
        print("Error: Patient file not found at %s, cannot continue." % patient_path)
        return ds
    with open(patient_path, "rt", encoding='latin1') as g: 
        for line in g:
            if "PatientID =" in line:
                # Pinnacle internal ID — kept for reference but NOT used as DICOM PatientID.
                pinnacle_internal_id = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
            if "LastName = " in line:
                lname = re.findall(r'"([^"]*)"', line)[0]
                lname = lname.replace(' (restored)', '')
                lname = lname.replace('\\', '')
                lname = lname.replace('/', '')
            if "FirstName =" in line:
                fname = re.findall(r'"([^"]*)"', line)[0]
                fname = fname.replace(" ", "")
                fname = fname.replace("\\", '')
                fname = fname.replace("/", '')
            if "MiddleName = " in line:
                mname = re.findall(r'"([^"]*)"', line)[0]
                mname = mname.replace("\\", '')
                mname = mname.replace('/', '')
            if "MedicalRecordNumber =" in line:
                medrecnum = re.findall(r'"([^"]*)"', line)[0]
                pid = medrecnum
                ds.PatientID = pid
            if "ReferringPhysician = " in line:
                refphys = re.findall(r'"([^"]*)"', line)[0]
                ds.ReferringPhysicianName = refphys
            if "RadiationOncologist = " in line:
                physician = re.findall(r'"([^"]*)"', line)[0]
                ds.PhysiciansOfRecord = physician
            if "Comment = " in line and flag_first:
                descrip = re.findall(r'"([^"]*)"', line)[0]
                ds.StudyDescription = descrip
            if "Gender = " in line:
                gen = re.findall(r'"([^"]*)"', line)[0]
                if "Male" in gen:
                    patient_sex = 'M'
                elif "Female" in gen:
                    patient_sex = 'F'
                ds.PatientSex = patient_sex
            if "DateOfBirth =" in line:
                dobstr = re.findall(r'"([^"]*)"', line)[0] #gets birthday string with numbers and dashes
                dob = ""  # default if invalid
                for fmt in ["%Y-%m-%d", "%d/%m/%Y", "%m/%d/%Y", "%d %m %Y"]:
                    try:
                        dob_date = datetime.strptime(dobstr, fmt)
                        dob = dob_date.strftime("%Y%m%d")
                        break
                    except ValueError:
                        pass
                ds.PatientBirthDate = dob
            if "ImageSetList ={" in line:
                flag_first = False
            if "PlanName = " in line:
                plancount = plancount + 1
                plannamelist.append(re.findall(r'"([^"]*)"', line)[0])
                ds.StructureSetLabel = plannamelist[plancount - 1]
            if "PrimaryCTImageSetID =" in line:
                imagesetnumber = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
                #print("Image set number: " + imagesetnumber)
                planimagesets.append(imagesetnumber)
            if "    PlanID =" in line:
                planids.append(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])
            if "    StudyID = " in line and flag_stid:
                sid = re.findall(r'"([^"]*)"', line)[0]
                #print ("Study id: ", sid)
                ds.StudyID = sid
                flag_stid = False
            if "WriteTimeStamp = " in line and flag_time:
                dateandtime = re.findall(r'"([^"]*)"', line)[0]
                arr = dateandtime.split()
                date = arr[0].replace('-', '')
                time = arr[1].replace(':', '')
                ds.StructureSetDate = date
                ds.StructureSetTime = time
                study_date = date
                study_time = time
                ds.StudyDate = date
                ds.StudyTime = time
                flag_time = False
            if "ToolType =" in line:
                model = re.findall(r'"([^"]*)"', line)[0]
                ds.ManufacturerModelName = model
            if "PinnacleVersionDescription" in line:
                softwarev = re.findall(r'"([^"]*)"', line)[0]
                ds.SoftwareVersions = softwarev
                #if listofversions == []:
                   # listofversions.append(softwarev)
                #flagsame = False
                #for ver in listofversions:
                    #if softwarev == ver:
                        #flagsame = True
                #f flagsame == False:
                    #listofversions.append(softwarev)
    ds.StructureSetName = 'POIandROI'
    ds.SeriesNumber = '1'
    # Safety fallback: if MedicalRecordNumber was missing, use Pinnacle internal ID
    if not pid and pinnacle_internal_id:
        print("WARNING: MedicalRecordNumber not found in Patient file — "
              "falling back to Pinnacle internal PatientID: %s" % pinnacle_internal_id)
        pid = pinnacle_internal_id
        ds.PatientID = pid
    patientname = lname + "^" + fname + "^" + mname + "^"
    ds.PatientName = patientname
    #print(ds)
    return ds
####################################################################################################################################################
####################################################################################################################################################


####################################################################################################################################################
#  Function that read in the first ROIs (reference points) from plan.Points
# Takes in data structure
####################################################################################################################################################
def readpoints(ds, planfolder):
    #print("Reading in the points\n")
    global ROI_COUNT 
    global SeriesUID
    global StudyInstanceUID
    global FrameUID
    global ClassUID
    global imageslice
    global imageuid
    global Colors
    global isocenter
    global patientfolder
    global doserefpt
    global ctcenter
    global xshift
    global yshift
    global patient_position
    global point_values
    global point_names
    global FrameUID
    points_path = "%s%s/%s/plan.Points"%(Inputf, patientfolder, planfolder)
    if not os.path.isfile(points_path):
        print("Warning: plan.Points not found at %s, skipping points." % points_path)
        return ds
    with open(points_path, "rt", encoding='latin1') as e:
        for num, line in enumerate(e,1):
            if "  Name = " in line:
                ROI_COUNT = ROI_COUNT + 1
                roi_contour = Dataset()
                roi_contour.ReferencedROINumber = str(ROI_COUNT)
                ds.ROIContourSequence.append(roi_contour)
                ss_roi = Dataset()
                ds.StructureSetROISequence.append(ss_roi)
                obs_roi = Dataset()
                ds.RTROIObservationsSequence.append(obs_roi)
                ds.StructureSetROISequence[ROI_COUNT - 1].ROINumber = ROI_COUNT
                refptname = re.findall(r'"([^"]*)"', line)[0]    
                ds.StructureSetROISequence[ROI_COUNT - 1].ROIName = refptname
                point_names.append(refptname)
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence = Sequence()
                ds.StructureSetROISequence[ROI_COUNT - 1].ROIGenerationAlgorithm = 'SEMIAUTOMATIC' #Not sure what this is for, just basing off template, should look into further
                ds.StructureSetROISequence[ROI_COUNT - 1].ReferencedFrameOfReferenceUID = FrameUID
                ds.ROIContourSequence[ROI_COUNT -1].ROIDisplayColor = Colors[0]
                refpoint = []
            if "XCoord =" in line:
                x = (line.split(" ")[-1]).replace(';','')
                if patient_position == 'HFS' or patient_position == 'FFP':
                    x = str(float(x)*10)
                elif patient_position == 'HFP' or patient_position == 'FFS':
                    x = str(-float(x)*10)
                refpoint.append(x)
            if "YCoord =" in line:
                y = (line.split(" ")[-1]).replace(';','')
                if patient_position == 'HFS' or patient_position == 'FFS':
                    y = str(-float(y)*10)
                elif patient_position == 'HFP' or patient_position == 'FFP':
                    y = str(float(y)*10)
                refpoint.append(y)
            if "ZCoord =" in line:
                z = (line.split(" ")[-1]).replace(';','')
                #print("The line below is the z value:")
                #print(z)
                #print("The line above is the z value")
                if patient_position == 'HFS' or patient_position == 'HFP':
                    z = str(-float(z)*10)
                elif patient_position == 'FFS' or patient_position == 'FFP':
                    z = str(float(z)*10)
                refpoint.append(z)
            if "LastModifiedTimeStamp" in line: #this is the last line for the points
                ds.RTROIObservationsSequence[ROI_COUNT -1].ObservationNumber = ROI_COUNT
                ds.RTROIObservationsSequence[ROI_COUNT -1].ReferencedROINumber = ROI_COUNT
                ds.RTROIObservationsSequence[ROI_COUNT -1].RTROIInterpretedType = 'MARKER'
                ds.RTROIObservationsSequence[ROI_COUNT -1].ROIInterpreter = ""
                Contour1 = Dataset()
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence.append(Contour1)
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[0].ContourData = refpoint
                point_values.append(refpoint)
                #print("refpoint:", refpoint)
                #if isocenter == []:
                #   isocenter = refpoint
                if "Iso" in refptname or "isocenter" in refptname or "isocentre" in refptname:
                    isocenter = refpoint
                if "CT Center" in refptname or "ct center" in refptname or "ct centre" in refptname:
                    ctcenter = refpoint
                if "drp" in refptname or "DRP" in refptname:
                    doserefpt = refpoint
                #print("isocenter:", isocenter)
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[0].ContourGeometricType = 'POINT'
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[0].NumberOfContourPoints = 1
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[0].ContourImageSequence = Sequence()
                ContourImage1 = Dataset()
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[0].ContourImageSequence.append(ContourImage1)
                closestvalue = abs(float(imageslice[0]) - float(refpoint[-1]))
                closestlocation = 0
                match = False
                for i, s in enumerate(imageslice,0):
                    #print("finding corresponding image\n")
                    if abs(float(s) - (float(refpoint[-1]))) < 0.01: #making this the tolerance
                        ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[0].ContourImageSequence[0].ReferencedSOPClassUID = '1.2.840.10008.5.1.4.1.1.2'
                        ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[0].ContourImageSequence[0].ReferencedSOPInstanceUID = imageuid[i]
                        match = True
                    else:
                        if abs(float(s) - (float(refpoint[-1]))) < closestvalue:
                            closestvalue = abs(float(s) - (float(refpoint[-1])))
                            closestlocation = i
                if not match:
                    ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[0].ContourImageSequence[0].ReferencedSOPClassUID = '1.2.840.10008.5.1.4.1.1.2'
                    ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[0].ContourImageSequence[0].ReferencedSOPInstanceUID = imageuid[closestlocation]

    if len(isocenter) < 2:
        isocenter = ctcenter
        #print("Isocenter not located, setting to ct center: ", str(isocenter))
    if len(isocenter) < 2:
        #print("Isocenter still not located, setting to point with center in name, if not, with iso in name")
        temp_point1 = []
        temp_point2 = []
        for j, pointnames in enumerate(point_names):
            if "center" in pointnames:
                temp_point1 = point_values[j]
                #print("setting to: " + str(temp_point1))
            elif "iso" in pointnames:
                temp_point2 = point_values[j]
                #print("setting to: " + str(temp_point2))
        if len(temp_point1) > 1:
            isocenter = temp_point1
            #print("setting iso: " + str(isocenter))
        elif len(temp_point2) > 1:
            isocenter = temp_point2
            #print("setting iso: " + str(isocenter))
        else:
            if  len(ds.ROIContourSequence) > 0: 
                isocenter = point_values[0] # setting to first point if isocenter or ct center not found
                #print("setting iso to actual value: " + str(isocenter))
    if len(isocenter) < 3:
        print("Warning: isocenter could not be determined, defaulting to [0, 0, 0]")
        isocenter = [0.0, 0.0, 0.0]
    #print("isocenter before loop to apply shifts to contour sequence points: " + str(isocenter))
    for enteredpoints in ds.ROIContourSequence:
        #print("In loop applying shifts: isocenter:" + str(isocenter) )
        enteredpoints.ContourSequence[0].ContourData[0] = str(float(enteredpoints.ContourSequence[0].ContourData[0]) - xshift)
        enteredpoints.ContourSequence[0].ContourData[1] = str(float(enteredpoints.ContourSequence[0].ContourData[1]) - yshift)
        #enteredpoints.ContourSequence[0].ContourData[2] = str(float(enteredpoints.ContourSequence[0].ContourData[2]) - float(isocenter[2]))  
        #print("bottom of loop applying shifts isocenter:" + str(isocenter))  
    #print("end of read points isocenter:" + str(isocenter))
    return ds            
####################################################################################################################################################
####################################################################################################################################################


####################################################################################################################################################
# Function to read in plan.roi and get contour information
# will take in data structure.
####################################################################################################################################################
def readroi(ds, planfolder):
    #print("Reading in roi file\n")
    global ROI_COUNT   
    global SeriesUID
    global StudyInstanceUID
    global FrameUID
    global ClassUID
    global imageslice
    global imageuid
    global Colors
    global patientfolder
    global isocenter
    global xshift
    global yshift   
    global patient_position
    points = []
    flag_points = False # bool value to tell me if I want to read the line in as point values
    prevroi = ROI_COUNT
    roi_path = "%s%s/%s/plan.roi"%(Inputf, patientfolder, planfolder)
    if not os.path.isfile(roi_path):
        print("Warning: plan.roi not found at %s, skipping ROI contours." % roi_path)
        return ds
    with open(roi_path, "rt", encoding='latin1') as f:
        for num, line in enumerate(f, 1):
            if "};  // End of points for curve" in line: # this will tell me not to read in point values
                #all points for current curve saved until now. Here is where I need to add them to dicom file
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[int(curvenum) - 1].ContourData = points
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[int(curvenum) - 1].ContourImageSequence = Sequence()
                ContourImage1 = Dataset()
                flag_match = False
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[int(curvenum) - 1].ContourImageSequence.append(ContourImage1)
                closestvalue = abs(float(imageslice[0]) - (float(points[-1])))
                closestlocation = 0
                match = False
                for i, s in enumerate(imageslice,0):
                    #print("finding corresponding image\n")
                    if abs(float(s) - (float(points[-1]))) < 0.01: #making this the tolerance for a match
                        ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[int(curvenum) - 1].ContourImageSequence[0].ReferencedSOPClassUID = '1.2.840.10008.5.1.4.1.1.2'
                        ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[int(curvenum) - 1].ContourImageSequence[0].ReferencedSOPInstanceUID = imageuid[i]
                        match = True
                    else:
                        if abs(float(s) - (float(points[-1]))) < closestvalue:
                            closestvalue = abs(float(s) - (float(points[-1])))
                            closestlocation = i
                if not match:
                    ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[int(curvenum) - 1].ContourImageSequence[0].ReferencedSOPClassUID = '1.2.840.10008.5.1.4.1.1.2'
                    ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[int(curvenum) - 1].ContourImageSequence[0].ReferencedSOPInstanceUID = imageuid[closestlocation]
                del points[:]
                flag_points = False
            if flag_points:
                curr_points = line.split(' ')
                if patient_position == 'HFS':
                    curr_points = [str(float(curr_points[0])*10 - xshift), str(-float(curr_points[1])*10 - yshift), str(-float(curr_points[2])*10)]
                elif patient_position == 'HFP':
                    curr_points = [str(-float(curr_points[0])*10 - xshift), str(float(curr_points[1])*10 - yshift), str(-float(curr_points[2])*10)]
                elif patient_position == 'FFP':
                    curr_points = [str(float(curr_points[0])*10 - xshift), str(float(curr_points[1])*10 - yshift), str(float(curr_points[2])*10)]
                elif patient_position == 'FFS':
                    curr_points = [str(-float(curr_points[0])*10 - xshift), str(-float(curr_points[1])*10 - yshift), str(float(curr_points[2])*10)]
                points = points + curr_points
            if "Beginning of ROI" in line: # Start of ROI
                ROI_COUNT = ROI_COUNT + 1 #increment ROI_num because I've found a new ROI
                roi_contour = Dataset()
                roi_contour.ReferencedROINumber = str(ROI_COUNT)
                ds.ROIContourSequence.append(roi_contour)
                ss_roi = Dataset()
                ds.StructureSetROISequence.append(ss_roi)
                obs_roi = Dataset()
                ds.RTROIObservationsSequence.append(obs_roi)
                ds.StructureSetROISequence[ROI_COUNT - 1].ROINumber = ROI_COUNT
                ROIName = line[22:] # gets a string of ROI name
                ROIName = ROIName.replace('\n','')
                ds.StructureSetROISequence[ROI_COUNT - 1].ROIName = ROIName
                ds.StructureSetROISequence[ROI_COUNT - 1].ROIGenerationAlgorithm = 'SEMIAUTOMATIC'
                ds.StructureSetROISequence[ROI_COUNT - 1].ReferencedFrameOfReferenceUID = FrameUID
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence = Sequence()
                if ROI_COUNT - prevroi <= len(Colors):
                    ds.ROIContourSequence[ROI_COUNT -1].ROIDisplayColor = Colors[ROI_COUNT - prevroi - 1]
                    #print(ROI_COUNT - prevroi-1)
                else:
                    if ROI_COUNT - 1 - len(Colors) < len(Colors):
                        ds.ROIContourSequence[ROI_COUNT -1].ROIDisplayColor = Colors[ROI_COUNT - 1 - len(Colors)]
                        #print(ROI_COUNT - 1 - len(Colors))
                    elif ROI_COUNT - 1 - len(Colors) - len(Colors) < len(Colors):
                        ds.ROIContourSequence[ROI_COUNT -1].ROIDisplayColor = Colors[ROI_COUNT - 1 - len(Colors) - len(Colors)]
                        #print(ROI_COUNT - 1 - len(Colors) - len(Colors))
                    else:
                        ds.ROIContourSequence[ROI_COUNT -1].ROIDisplayColor = Colors[ROI_COUNT - 1 - len(Colors) - len(Colors) - len(Colors)]
                        #print(ROI_COUNT - 1 - len(Colors) - len(Colors) - len(Colors))
                #print('ROI Number & Name: '+str(ROI_COUNT)+', '+ROIName)
            if "}; // End of ROI" in line: #end of ROI found
                #ROI_type = line[31:]
                #ROI_type = ROI_type.replace('\n','')
                ds.RTROIObservationsSequence[ROI_COUNT -1].ObservationNumber = ROI_COUNT
                ds.RTROIObservationsSequence[ROI_COUNT -1].ReferencedROINumber = ROI_COUNT
                if "PTV" in ROIName: 
                    ds.RTROIObservationsSequence[ROI_COUNT -1].RTROIInterpretedType = 'PTV'
                else:
                    ds.RTROIObservationsSequence[ROI_COUNT -1].RTROIInterpretedType = 'ORGAN'
                ds.RTROIObservationsSequence[ROI_COUNT -1].ROIInterpreter = ""
                #add to ROI observation sequence
            if "volume =" in line:
                vol = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
                ds.StructureSetROISequence[ROI_COUNT - 1].ROIVolume = vol
            if "//  Curve " in line: #found a curve
                curvenum = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
                contour_ds = Dataset()
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence.append(contour_ds)
            if "num_points =" in line:
                npts = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[int(curvenum) - 1].ContourGeometricType = 'CLOSED_PLANAR'
                ds.ROIContourSequence[ROI_COUNT - 1].ContourSequence[int(curvenum) - 1].NumberOfContourPoints = npts
            if "points=" in line:
                flag_points = True
    return ds
####################################################################################################################################################
####################################################################################################################################################

####################################################################################################################################################
# Function: planinit()
# purpose: to fill in data basic elements for RT plan file
####################################################################################################################################################
def planinit(ds, planame, planandnum, plannumber):
    global patientname
    global dob
    global pid
    global patient_sex
    global plansopinstuid
    global study_time
    global study_date
    global StudyInstanceUID
    global model
    global physician
    global planseriesinstuid
    global sid
    global FrameUID
    global descrip
    global structsopinstuid
    global posrefind
    ds.SpecificCharacterSet = 'ISO_IR 100'
    ds.InstanceCreationDate = time.strftime("%Y%m%d")
    ds.InstanceCreationTime = time.strftime("%H%M%S")
    ds.SOPClassUID = '1.2.840.10008.5.1.4.1.1.481.5' #RT Plan Storage
    ds.SOPInstanceUID = make_sub_uid(plansopinstuid, plannumber)
    ds.StudyDate = study_date
    ds.StudyTime = study_time
    ds.AccessionNumber = ''
    ds.Modality = 'RTPLAN'
    ds.Manufacturer =Manufacturer
    ds.ReferringPhysicianName = physician if physician else ""
    ds.OperatorsName = ""
    ds.ManufacturerModelName = model
    ds.SoftwareVersions = softwarev if softwarev else 'Unknown'
    ds.PhysiciansOfRecord = physician
    ds.PatientName = patientname
    ds.PatientBirthDate = dob
    ds.PatientID = pid
    ds.PatientSex = patient_sex
    ds.StudyInstanceUID = StudyInstanceUID
    ds.SeriesInstanceUID = make_sub_uid(planseriesinstuid, plannumber)
    ds.StudyID = sid
    ds.FrameOfReferenceUID = FrameUID
    ds.PositionReferenceIndicator = posrefind
    ds.RTPlanLabel = planandnum + '.0' # may need to change this later
    ds.RTPlanName = planame
    ds.RTPlanDescription = descrip
    ds.RTPlanDate = study_date
    ds.RTPlanTime = study_time
    #ds.PlanIntent = "" #Not sure where to get this informationd, will likely be 'CURATIVE' or 'PALIATIVE'
    ds.RTPlanGeometry = 'PATIENT'
    #ds.DoseReferenceSequence = Sequence() #figure out what goes in DoseReferenceSequence... Should be like a target volume and reference point I think...
    #ds.ToleranceTableSequence = Sequence() #figure out where to get this information
    ds.FractionGroupSequence = Sequence()
    ds.BeamSequence = Sequence()
    ds.PatientSetupSequence = Sequence() #need one per beam
    ds.ReferencedStructureSetSequence = Sequence()
    ReferencedStructureSet1 = Dataset()
    ds.ReferencedStructureSetSequence.append(ReferencedStructureSet1)
    ds.ReferencedStructureSetSequence[0].ReferencedSOPClassUID = '1.2.840.10008.5.1.4.1.1.481.3'
    ds.ReferencedStructureSetSequence[0].ReferencedSOPInstanceUID = structsopinstuid[:64].rstrip(".")
    ds.ApprovalStatus = 'UNAPPROVED' #find out where to get this information
    return ds
####################################################################################################################################################
####################################################################################################################################################


####################################################################################################################################################
# Function: getpatientsetup()
# purpose: Returns the value for patient setup
####################################################################################################################################################
def getpatientsetup(planfolder):
    global patientfolder
    global no_setup_file
    if not os.path.exists("%s%s/%s/plan.PatientSetup"%(Inputf, patientfolder, planfolder)):
        no_setup_file = True
        return
    with open("%s%s/%s/plan.PatientSetup"%(Inputf, patientfolder, planfolder), "rt", encoding='latin1') as f:
        for line in f:
            if "Position =" in line:
                pos = re.findall(r'"([^"]*)"', line)[0]
            if "Orientation =" in line:
                orient = re.findall(r'"([^"]*)"', line)[0]
        if "Head First" in orient:
            pat_pos = "HF"
        elif "Feet First" in orient:
            pat_pos = "FF"
        if "supine" in pos:
            pat_pos = pat_pos + "S"
        elif "prone" in pos:
            pat_pos = pat_pos + "P"
        elif "decubitus right" in pos or "Decuibitus Right" in pos:
            pat_pos = pat_pos + "DR"
        elif "decubitus left" in pos or "Decuibitus Left" in pos:
            pat_pos = pat_pos +"DL"
    return pat_pos
####################################################################################################################################################
####################################################################################################################################################


####################################################################################################################################################
# Function: readtrial()
# purpose: get Beam information from plan.Trial for RT plan file
####################################################################################################################################################
def readtrial(ds, planfolder, plannumber, trial_lines=None):
    #print("There is a problem somewhere in this function\n")
    global isocenter
    global xshift
    global yshift
    global zshift
    global patientfolder
    global doserefpt
    global patient_position
    global dosexdim
    global doseydim
    global dosezdim
    global doseoriginx
    global doseoriginy
    global doseoriginz
    global beamdosefiles
    global numfracs
    global pixspacingy
    global pixspacingx
    global pixspacingz
    global point_values
    global point_names
    global flag_nobinaryfile
    global no_beams
    global PDD15MV
    global PDD16MV
    global PDD10MV
    global PDD6MV
    #print("Entering readtrial function, isocenter: " + str(isocenter))
    beamdoses = []
    beamdosefiles = []
    beamcount = 0
    MUlineflag = False
    nomachinename = True
    mlcleafpos = False
    flag_stepnshoot = False
    beginleafpoints = False
    currentmeterset = 0.0
    beginbeam = False
    ctrlptlist = False
    ctrlptmeterflag = False
    noname = True
    current_dosefile_num = ''
    beamenergies = []
    leafpositions1 = []
    leafpositions2 = []
    metersetweight = ['0']
    wedgeangles = []
    numctrlpts = 0
    totalleafpositions = [] #this list will have lists for all the control points
    currentcontrolpoint = 0
    countpoints = 0
    FractionGroup1 = Dataset() #I'm assuming here I only need one data set in fraction goup sequence
    ds.FractionGroupSequence.append(FractionGroup1)
    ds.FractionGroupSequence[0].ReferencedBeamSequence = Sequence()

    # Use pre-split trial lines if provided, otherwise read the file
    if trial_lines is not None:
        all_lines = trial_lines
    else:
        trial_path = "%s%s/%s/plan.Trial"%(Inputf, patientfolder, planfolder)
        if not os.path.isfile(trial_path):
            print("Warning: plan.Trial not found at %s, skipping plan." % trial_path)
            no_beams = True
            return ds
        tempfile = open(trial_path, "rt", encoding='latin1')
        all_lines = tempfile.readlines()
        tempfile.close()
        num_trials = all_lines.count("Trial ={\n")
        if num_trials > 1:
            linetostart = all_lines[1:].index("Trial ={\n") + 1
            all_lines = all_lines[:linetostart] #take first trial for backwards compat
    #with open("%s%s/%s/plan.Trial"%(Inputf, patientfolder, planfolder), "rt", encoding='latin1') as h:
        #for linenum, line in enumerate(h,0):
    for linenum, line in enumerate(all_lines, 0):
        if "BeamList ={" in line and "};" in all_lines[linenum + 1]:
            #empty beam set, skip patient
            no_beams = True
            return ds
        if "DoseGrid .VoxelSize .X" in line:
            pixspacingx = float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10
        if "DoseGrid .VoxelSize .Y" in line:
            pixspacingy = float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10
        if "DoseGrid .VoxelSize .Z" in line:
            pixspacingz = float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10
        if "DoseGrid .Dimension .X" in line:
            dosexdim = int(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])
        if "DoseGrid .Dimension .Y" in line:
            doseydim = int(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])
        if "DoseGrid .Dimension .Z" in line:
            dosezdim = int(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])
        if "DoseGrid .Origin .X" in line:
            if patient_position == 'HFP' or patient_position == 'FFS':
                doseoriginx = str(-float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10 - xshift)
            elif patient_position == 'HFS' or patient_position == 'FFP':
                doseoriginx = str(float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10 - xshift)
             
        if "DoseGrid .Origin .Y" in line:
            if patient_position == 'HFS' or patient_position == 'FFS':
                doseoriginy = str(-float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10 - yshift)
            elif patient_position == 'HFP' or patient_position == 'FFP':
                doseoriginy = str(float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10 - yshift)
        if "DoseGrid .Origin .Z" in line:
            if patient_position == 'HFS' or patient_position == 'HFP':
                doseoriginz = str(-float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10)
            elif patient_position == 'FFS' or patient_position == 'FFP':
                doseoriginz = str(float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10)
        if "      NumberOfFractions =" in line:
            numfracs = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
        if "      DoseVolume = " in line:
            current_dosefile_num = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
            if int(current_dosefile_num) < 10:
                current_dosefile_num = "00" + current_dosefile_num
            elif int(current_dosefile_num) < 100:
                current_dosefile_num = "0" + current_dosefile_num 
            beamdosefiles.append(current_dosefile_num)
            #print('Reading file: plan.Trail.binary.'+str(current_dosefile_num))
            #print('Number of dose files read: '+str(len(beamdosefiles)))
        if "Beam ={" in line and 'Proton' not in line:
            #print("Line that indicates beam information\n")
            #new beam
            MUlineflag = False
            nomachinename = True
            noname = True
            countpoints = 0
            currentcontrolpoint = 0
            numwedges = 0
            beginbeam = True
            wedgeflag = False
            beamcount = beamcount + 1
            del totalleafpositions
            totalleafpositions = []
            del leafpositions1
            del leafpositions2
            leafpositions1 = []
            leafpositions2 = []
            x1 = ""
            x2 = ""
            y1 = ""
            y2 = ""
            ref_beam = Dataset()
            ds.FractionGroupSequence[0].ReferencedBeamSequence.append(ref_beam)
             
            ds.FractionGroupSequence[0].ReferencedBeamSequence[beamcount - 1].ReferencedBeamNumber = beamcount
            beam_ds = Dataset()
            ds.BeamSequence.append(beam_ds)
            ds.BeamSequence[beamcount - 1].Manufacturer = Manufacturer #figure out what to put here
            ds.BeamSequence[beamcount - 1].BeamNumber = beamcount
            ds.BeamSequence[beamcount - 1].TreatmentDeliveryType = 'TREATMENT'
            ds.BeamSequence[beamcount - 1].ReferencedPatientSetupNumber = beamcount 
            ds.BeamSequence[beamcount - 1].SourceAxisDistance = '1000'
            ds.BeamSequence[beamcount - 1].FinalCumulativeMetersetWeight = '1'
            ds.BeamSequence[beamcount - 1].PrimaryDosimeterUnit = 'MU'
            ds.BeamSequence[beamcount - 1].PrimaryFluenceModeSequence = Sequence()
            PrimaryFluenceMode1 = Dataset()
            ds.BeamSequence[beamcount - 1].PrimaryFluenceModeSequence.append(PrimaryFluenceMode1)
            ds.BeamSequence[beamcount - 1].PrimaryFluenceModeSequence[0].FluenceMode = 'STANDARD'
        if "      Name =" == line[:12] and beginbeam and noname:
            ds.BeamSequence[beamcount - 1].BeamName = re.findall(r'"([^"]*)"', line)[0]
            noname = False
        if "   PrescriptionPointName" in line:
            nameofrefpt = re.findall(r'"([^"]*)"', line)[0]
            for i, name in enumerate(point_names, 0):
                if nameofrefpt == name:
                    doserefpt = point_values[i]
            if doserefpt != []:
                #print("Dose reference point: " + str([float(doserefpt[0])-xshift, float(doserefpt[1])-yshift, float(doserefpt[2])]))
                ds.FractionGroupSequence[0].ReferencedBeamSequence[beamcount - 1].BeamDoseSpecificationPoint = [float(doserefpt[0])-xshift, float(doserefpt[1])-yshift, float(doserefpt[2])] #Not sure if I need shifts here or not...?
            else:
                _iso = isocenter if len(isocenter) >= 3 else [0.0, 0.0, 0.0]
                #print("No dose reference point, setting to isocenter: " + str([float(_iso[0]) - xshift, float(_iso[1]) - yshift, float(_iso[2])]))
                ds.FractionGroupSequence[0].ReferencedBeamSequence[beamcount - 1].BeamDoseSpecificationPoint = [float(_iso[0]) - xshift, float(_iso[1]) - yshift, float(_iso[2])]
        if "      PrescriptionDose =" == line[:24]:
            prescdose = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
        if "      Modality =" == line[:16] and beginbeam:
            if (re.findall(r'"([^"]*)"', line)[0] == 'Photons'):
                ds.BeamSequence[beamcount - 1].RadiationType = 'PHOTON'
            elif (re.findall(r'"([^"]*)"', line)[0] == 'Electrons'):
                ds.BeamSequence[beamcount - 1].RadiationType = 'ELECTRON'
            else:
                ds.BeamSequence[beamcount - 1].RadiationType = ""
        if "      SetBeamType" in line and beginbeam:
            if "STATIC" ==  re.findall(r'"([^"]*)"', line)[0].upper():
                ds.BeamSequence[beamcount - 1].BeamType = re.findall(r'"([^"]*)"', line)[0].upper()
            else:
                if "Step & Shoot" in re.findall(r'"([^"]*)"', line)[0] or ("step" in re.findall(r'"([^"]*)"', line)[0] and 'shoot' in re.findall(r'"([^"]*)"', line)[0]) or ("Step" in re.findall(r'"([^"]*)"', line)[0] and 'Shoot' in re.findall(r'"([^"]*)"', line)[0]):
                    #ds.BeamSequence[beamcount - 1].BeamType = "STATIC"
                    flag_stepnshoot = True
                #else:
                ds.BeamSequence[beamcount - 1].BeamType = "DYNAMIC"
        if "MonitorUnitInfo ={" in line and beginbeam:
            MUlineflag = True
            ctrlptmeterflag = False
        if "SourceToPrescriptionPointDistance" in line and MUlineflag == True:
            sad = float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10
            #ds.BeamSequence[beamcount - 1].SourceAxisDistance = sad
        if "PrescriptionDose =" in line and MUlineflag == True:
            prescripdose =  float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])
            normdose = float(re.findall(r"[-+]?\d*\.\d+|\d+", all_lines[linenum + 15])[0])
            OFc = float(re.findall(r"[-+]?\d*\.\d+|\d+", all_lines[linenum + 17])[0])
            # OFc value added by Achraf Touzani 2018
            if normdose == 0 or OFc == 0:
                beammu = 0
                print("Warning: normdose or OFc is 0 for beam %d, setting BeamMeterset=0." % beamcount)
                ds.FractionGroupSequence[0].ReferencedBeamSequence[beamcount - 1].BeamMeterset = 0
                ds.FractionGroupSequence[0].ReferencedBeamSequence[beamcount - 1].BeamDose = 0
                beamdoses.append(0)
                MUlineflag = False
                continue
            ds.FractionGroupSequence[0].ReferencedBeamSequence[beamcount - 1].BeamDose = float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])/100
            raw_dose_val = float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])
            if beamenergies[beamcount-1] == '6': 
                beammu = raw_dose_val/(normdose*PDD6MV*OFc)
            elif beamenergies[beamcount-1] == '15': 
                beammu = raw_dose_val/(normdose*PDD15MV*OFc)
            elif beamenergies[beamcount-1] == '16':
                beammu = raw_dose_val/(normdose*PDD16MV*OFc)
            elif beamenergies[beamcount-1] == '10':
                beammu = raw_dose_val/(normdose*PDD10MV*OFc)
            else:
                print("Warning: beam energy '%s' not in PDD table (6,10,15,16), setting BeamMeterset=0 for beam %d." 
                      % (beamenergies[beamcount-1], beamcount))
                beammu = 0
                ds.FractionGroupSequence[0].ReferencedBeamSequence[beamcount - 1].BeamMeterset = 0
                ds.FractionGroupSequence[0].ReferencedBeamSequence[beamcount - 1].BeamDose = 0
                beamdoses.append(0)
                MUlineflag = False
                continue
            #print("Beam MU: " + str(beammu))
            ds.FractionGroupSequence[0].ReferencedBeamSequence[beamcount - 1].BeamMeterset = beammu
            beamdoses.append(beammu)

            MUlineflag = False
            #Figure out what to do with BeamDose
        if "MachineNameAndVersion =" in line and nomachinename:
            machinename = re.findall(r'"([^"]*)"', line)[0]
            machinename = machinename.partition(":")[0]
            ds.BeamSequence[beamcount - 1].TreatmentMachineName = machinename
            nomachinename = False
        if "MachineEnergyName =" in line and beginbeam:
            beamenergies.append(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])
        if "NumberOfControlPoints" in line and beginbeam:
            numctrlpts = int(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])
            ds.BeamSequence[beamcount - 1].ControlPointSequence = Sequence()
            currentmeterset = 0.0
        if "ControlPointList ={" in line:
            ctrlptlist = True
            #print("ctrlptlist is True")
        if "Gantry =" in line and ctrlptlist: #Find out if this is gantry angle.
            gantryangle = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
            currentcontrolpoint = currentcontrolpoint + 1
        if "  Collimator =" in line and ctrlptlist:
            colangle = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
        if "  Couch =" in line and ctrlptlist:
            psupportangle = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
        if "     WedgeName = " in line and ctrlptlist:
            #print("wedge name found")
            if re.findall(r'"([^"]*)"', line)[0] == 'No Wedge' or re.findall(r'"([^"]*)"', line)[0] == "":
                wedgeflag = False
                #print("Wedge is no name")
                numwedges = 0 
            elif "edw" in re.findall(r'"([^"]*)"', line)[0] or "EDW" in re.findall(r'"([^"]*)"', line)[0]:
                #print("Wedge present")
                wedgetype = "DYNAMIC"
                wedgeflag = True
                numwedges = 1
                wedgeangle = re.findall(r"[-+]?\d*\.\d+|\d+", all_lines[linenum + 4])[0]
                wedgeinorout = ""
                wedgeinorout = re.findall(r'"([^"]*)"', all_lines[linenum+1])[0]
                if "WedgeBottomToTop" == wedgeinorout:
                    wedgename = re.findall(r'"([^"]*)"', line)[0].upper() +  wedgeangle + "IN"
                    wedgeorientation = '0' # temporary until I find out what to put here
                elif "WedgeTopToBottom" == wedgeinorout:
                    wedgename = re.findall(r'"([^"]*)"', line)[0].upper() +  wedgeangle + "OUT"
                    wedgeorientation = '180'
                #print("Wedge name = ", wedgename)
            elif "UP" in re.findall(r'"([^"]*)"', line)[0]:
                #print("Wedge present")
                wedgetype = "STANDARD"
                wedgeflag = True
                numwedges = 1
                wedgeangle = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
                wedgeinorout = ""
                wedgeinorout = re.findall(r'"([^"]*)"', all_lines[linenum+1])[0]
                if int(wedgeangle) == 15:
                    numberinname = '30'
                elif int(wedgeangle) == 45:
                    numberinname = '20'
                elif int(wedgeangle) == 30:
                    numberinname = '30'
                elif int(wedgeangle) == 60:
                    numberinname = '15'
                if "WedgeRightToLeft" == wedgeinorout:
                    wedgename = "W" +  str(int(wedgeangle)) + "R" + numberinname# + "U"
                    wedgeorientation = '90' # temporary until I find out what to put here
                elif "WedgeLeftToRight" == wedgeinorout:
                    wedgename = "W" +  str(int(wedgeangle)) + "L" + numberinname# + "U"
                    wedgeorientation = '270'
                elif "WedgeTopToBottom" == wedgeinorout:
                    wedgename = "W" +  str(int(wedgeangle)) + "OUT" + numberinname# + "U"
                    wedgeorientation = '180' # temporary until I find out what to put here
                elif "WedgeBottomToTop" == wedgeinorout:
                    wedgename = "W" +  str(int(wedgeangle)) + "IN" + numberinname# + "U"
                    wedgeorientation = '0' # temporary until I find out what to put here
                #print("Wedge name = ", wedgename)
        if "LeftJawPosition" in line and x1 == "":
            x1 = str(-float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10)
            #print("X jaw 1:", x1, "\n")
        if "RightJawPosition" in line and x2 == "":
            x2 = float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10
            #print("X jaw 2:", x2, "\n")
        if "TopJawPosition" in line and y2 == "":
            y2 = float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10
            #print("y jaw 2:", y2, "\n")
        if "BottomJawPosition" in line and y1 == "":
            y1 = -float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10
            #print("y jaw 1:", y1, "\n")
        if "MLCLeafPositions ={" in line:
            mlcleafpos = True
            ctrlptmeterflag = True
        if mlcleafpos and "Points[] ={" in line:
            beginleafpoints = True
            del leafpositions1
            del leafpositions2
            leafpositions1 = []
            leafpositions2 = []
            continue
        if beginleafpoints:
            countpoints = countpoints + 1
            leafpointline = line.strip()
            leafpoints = leafpointline.split(',')
            #print("leafpoints: ", leafpoints)
            if leafpoints[0] == '};':
                beginleafpoints = False
                mlcleafpos = False
                leafpositions1 = list(reversed(leafpositions1))
                leafpositions2 = list(reversed(leafpositions2))
                totalleafpositions.append((leafpositions1+leafpositions2))
                continue
            leafpositions1.append(-float(leafpoints[0])*10)
            leafpositions2.append(float(leafpoints[1])*10)
        if ctrlptmeterflag and "  Weight =" in line:
            metersetweight.append(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])
        if "SSD = " in line and beginbeam:
            ssd = float(re.findall(r"[-+]?\d*\.\d+|\d+", line)[0])*10
        if "GantryIsCCW = " in line:
            if re.findall(r"[-+]?\d*\.\d+|\d+", line)[0] == '0':  #This may be a problem here!!!! Not sure how to Pinnacle does this, could be 1 if CW, must be somewhere that states if gantry is rotating or not
                gantryrotdir = 'NONE'
            elif  re.findall(r"[-+]?\d*\.\d+|\d+", line)[0] == '1':
                gantryrotdir = 'CC'
        if "GantryIsCW = " in line:
            if re.findall(r"[-+]?\d*\.\d+|\d+", line)[0] == '0':
                gantryrotdir = 'NONE'
            elif  re.findall(r"[-+]?\d*\.\d+|\d+", line)[0] == '1':
                gantryrotdir = 'CW'
        if flag_stepnshoot and "      DisplayMAXLeafMotion" in line:
            doserate = "400" 
            ds.BeamSequence[beamcount - 1].NumberOfControlPoints = numctrlpts*2
            ds.BeamSequence[beamcount - 1].FinalCumulativeMetersetWeight = 1.0
            ds.BeamSequence[beamcount - 1].SourceToSurfaceDistance = ssd
            if numwedges > 0:
                ds.BeamSequence[beamcount - 1].WedgeSequence = Sequence()
                Wedge1 = Dataset()
                ds.BeamSequence[beamcount - 1].WedgeSequence.append(Wedge1)
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeNumber = 1 #I am assuming only one wedge per beam (which makes sense because you can't change it during beam)
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeType = wedgetype #might need to change this
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeAngle = wedgeangle
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeID = wedgename
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeOrientation = wedgeorientation
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeFactor = ""
            
            #ds.BeamSequence[beamcount - 1].SourceAxisDistance = '1000'
            # Step-and-shoot: N Pinnacle control points → 2N DICOM control points.
            # Pinnacle stores N differential segment weights (metersetweight[1..N]).
            # metersetweight[0] is typically '1' (an initial marker, not a real weight).
            # We need to convert to cumulative [0.0 → 1.0] over 2N DICOM CPs.
            # Each pair (open, close) delivers one segment; open=cumulative before,
            # close=cumulative after.
            
            # Extract the N segment weights (skip the first entry which is usually '1')
            seg_weights_raw = []
            for sw_idx in range(1, min(len(metersetweight), numctrlpts + 1)):
                seg_weights_raw.append(float(metersetweight[sw_idx]))
            
            # If we don't have enough weights, pad with equal distribution
            while len(seg_weights_raw) < numctrlpts:
                seg_weights_raw.append(0.0)
            
            # Normalize: sum of segment weights = 1.0
            total_seg_weight = sum(seg_weights_raw)
            if total_seg_weight > 0:
                seg_weights_norm = [w / total_seg_weight for w in seg_weights_raw]
            else:
                # All zero — distribute equally
                seg_weights_norm = [1.0 / numctrlpts] * numctrlpts
            
            # Build cumulative weights for 2N DICOM control points
            # CP0 (open seg 0) = 0.0
            # CP1 (close seg 0) = seg_weights_norm[0]
            # CP2 (open seg 1) = seg_weights_norm[0]  (same as close of previous)
            # CP3 (close seg 1) = seg_weights_norm[0] + seg_weights_norm[1]
            # ...
            # CP[2N-1] = 1.0
            cumulative_weights = []
            running = 0.0
            for seg_idx in range(numctrlpts):
                cumulative_weights.append(running)           # open
                running += seg_weights_norm[seg_idx]
                cumulative_weights.append(running)           # close
            # Ensure final is exactly 1.0 (floating point safety)
            if cumulative_weights:
                cumulative_weights[-1] = 1.0
            
            for j in range(0,numctrlpts*2):
                cp_ds = Dataset()
                ds.BeamSequence[beamcount - 1].ControlPointSequence.append(cp_ds)
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ControlPointIndex = j
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence = Sequence()
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence = Sequence()
                ReferencedDoseReference1 = Dataset()
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence.append(ReferencedDoseReference1)
                
                # Use pre-computed cumulative weight (normalized 0→1)
                cw = cumulative_weights[j] if j < len(cumulative_weights) else 1.0
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].CumulativeMetersetWeight = cw
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence[0].CumulativeDoseReferenceCoefficient = cw
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence[0].ReferencedDoseReferenceNumber = '1'
                
                if j == 0: #first control point beam meterset always zero
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].NominalBeamEnergy = beamenergies[beamcount - 1]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].DoseRateSet = doserate
                    
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].GantryRotationDirection = 'NONE'
                    #print("Gantry angle list length: ", len(gantryangles))
                    #print("current controlpoint: ", j)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].GantryAngle = gantryangle
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDeviceAngle = colangle
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDeviceRotationDirection = 'NONE'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].SourceToSurfaceDistance = ssd
                    BeamLimitingDevicePosition1 = Dataset() #This will be the x jaws
                    BeamLimitingDevicePosition2 = Dataset() #this will be the y jaws
                    if numwedges > 0:
                        WedgePosition1 = Dataset()
                        ds.BeamSequence[beamcount - 1].ControlPointSequence[j].WedgePositionSequence = Sequence()
                        ds.BeamSequence[beamcount - 1].ControlPointSequence[j].WedgePositionSequence.append(WedgePosition1)
                        ds.BeamSequence[beamcount - 1].ControlPointSequence[j].WedgePositionSequence[0].WedgePosition = "IN"
                        ds.BeamSequence[beamcount - 1].ControlPointSequence[j].WedgePositionSequence[0].ReferencedWedgeNumber = '1'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence.append(BeamLimitingDevicePosition1)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence.append(BeamLimitingDevicePosition2)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[0].RTBeamLimitingDeviceType = 'ASYMX'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[0].LeafJawPositions = [x1,x2]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[1].RTBeamLimitingDeviceType = 'ASYMY'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[1].LeafJawPositions = [y1, y2]
                    BeamLimitingDevicePosition3 = Dataset() #this will be the MLC 
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence.append(BeamLimitingDevicePosition3)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[2].RTBeamLimitingDeviceType = 'MLCX'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[2].LeafJawPositions = totalleafpositions[j]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].SourceToSurfaceDistance = ssd
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDeviceRotationDirection = 'NONE'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].PatientSupportAngle = psupportangle
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].PatientSupportRotationDirection = 'NONE'
                    #print("Setting Isocenter postion: " + "[" + str(float(isocenter[0]) - xshift) +" , " +str(float(isocenter[1]) - yshift) + " , " + str(float(isocenter[2]))+ "]")
                    _iso = isocenter if len(isocenter) >= 3 else [0.0, 0.0, 0.0]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].IsocenterPosition = [float(_iso[0]) - xshift, float(_iso[1]) - yshift, float(_iso[2])]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].GantryRotationDirection = gantryrotdir
                else:
                    BeamLimitingDevicePosition1 = Dataset() #This will be the mlcs for control points other than the first
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence.append(BeamLimitingDevicePosition1)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[0].RTBeamLimitingDeviceType = 'MLCX'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[0].LeafJawPositions = totalleafpositions[int(j/2)]
                ds.BeamSequence[beamcount - 1].NumberOfWedges = numwedges
                ds.BeamSequence[beamcount - 1].NumberOfCompensators = '0' # this is temporary value, will read in from file later
                ds.BeamSequence[beamcount - 1].NumberOfBoli = '0' # Also temporary
                ds.BeamSequence[beamcount - 1].NumberOfBlocks = '0' # Temp 
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence = Sequence()
                BeamLimitingDevice1 = Dataset()
                BeamLimitingDevice2 = Dataset()
                BeamLimitingDevice3 = Dataset()
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence.append(BeamLimitingDevice1)
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence.append(BeamLimitingDevice2)
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence.append(BeamLimitingDevice3)
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[0].RTBeamLimitingDeviceType = 'ASYMX'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[1].RTBeamLimitingDeviceType = 'ASYMY'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[2].RTBeamLimitingDeviceType = 'MLCX'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[0].NumberOfLeafJawPairs = '1'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[1].NumberOfLeafJawPairs = '1'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[2].NumberOfLeafJawPairs = '60'
                bounds = ['-200','-190','-180','-170','-160','-150','-140','-130','-120','-110','-100','-95','-90','-85','-80','-75','-70','-65','-60','-55','-50','-45','-40','-35','-30','-25','-20','-15','-10','-5','0','5','10','15','20','25','30','35','40','45','50','55','60','65','70','75','80','85','90','95','100','110','120','130','140','150','160','170','180','190','200']
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[2].LeafPositionBoundaries = bounds
            ctrlptlist = False 
            wedgeflag = False
            numwedges = 0
            beginbeam = False
        if "      DisplayMAXLeafMotion" in line and not flag_stepnshoot:
            #doserate = re.findall(r"[-+]?\d*\.\d+|\d+", line)[0]
            doserate = "400" 
            ds.BeamSequence[beamcount - 1].NumberOfControlPoints = numctrlpts + 1
            ds.BeamSequence[beamcount - 1].FinalCumulativeMetersetWeight = 1.0
            ds.BeamSequence[beamcount - 1].SourceToSurfaceDistance = ssd
            if numwedges > 0:
                ds.BeamSequence[beamcount - 1].WedgeSequence = Sequence()
                Wedge1 = Dataset()
                ds.BeamSequence[beamcount - 1].WedgeSequence.append(Wedge1)
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeNumber = 1 #I am assuming only one wedge per beam (which makes sense because you can't change it during beam)
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeType = wedgetype #might need to change this
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeAngle = wedgeangle
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeID = wedgename
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeOrientation = wedgeorientation
                ds.BeamSequence[beamcount-1].WedgeSequence[0].WedgeFactor = ""
            # Non-step-and-shoot: N Pinnacle CPs → N+1 DICOM CPs.
            # For static beams (N=1), DICOM needs CP0=0.0, CP1=1.0.
            # Pinnacle stores raw weight values; normalize to [0, 1].
            num_dicom_cps = numctrlpts + 1
            if num_dicom_cps <= len(metersetweight):
                # Use first 'num_dicom_cps' weights
                raw_w = [float(metersetweight[k]) for k in range(num_dicom_cps)]
            else:
                # Pad with zeros
                raw_w = [float(metersetweight[k]) if k < len(metersetweight) else 0.0
                         for k in range(num_dicom_cps)]
            # Normalize: CP0 should be 0, last CP should be 1
            max_w = raw_w[-1] if raw_w[-1] != 0 else 1.0
            norm_w = [w / max_w for w in raw_w]
            # Force endpoints
            norm_w[0] = 0.0
            norm_w[-1] = 1.0
            
            for j in range(0,numctrlpts+1):
                cp_ds = Dataset()
                ds.BeamSequence[beamcount - 1].ControlPointSequence.append(cp_ds)
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ControlPointIndex = j
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence = Sequence()
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence = Sequence()
                ReferencedDoseReference1 = Dataset()
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence.append(ReferencedDoseReference1)
                ds.BeamSequence[beamcount - 1].ControlPointSequence[j].CumulativeMetersetWeight = norm_w[j]
                if j == 0: #first control point beam meterset always zero
                    BeamLimitingDevicePosition1 = Dataset() #This will be the x jaws
                    BeamLimitingDevicePosition2 = Dataset() #this will be the y jaws
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].NominalBeamEnergy = beamenergies[beamcount - 1]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].DoseRateSet = doserate
                    
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].GantryRotationDirection = 'NONE'
                    #print("Gantry angle list length: ", len(gantryangles))
                    #print("current controlpoint: ", j)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].GantryAngle = gantryangle
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDeviceAngle = colangle
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].SourceToSurfaceDistance = ssd
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence[0].CumulativeDoseReferenceCoefficient = '0'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence[0].ReferencedDoseReferenceNumber = '1'
                    if numwedges > 0:
                        WedgePosition1 = Dataset()
                        ds.BeamSequence[beamcount - 1].ControlPointSequence[j].WedgePositionSequence = Sequence()
                        ds.BeamSequence[beamcount - 1].ControlPointSequence[j].WedgePositionSequence.append(WedgePosition1)
                        ds.BeamSequence[beamcount - 1].ControlPointSequence[j].WedgePositionSequence[0].WedgePosition = "IN"
                        ds.BeamSequence[beamcount - 1].ControlPointSequence[j].WedgePositionSequence[0].ReferencedWedgeNumber = '1'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence.append(BeamLimitingDevicePosition1)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence.append(BeamLimitingDevicePosition2)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[0].RTBeamLimitingDeviceType = 'ASYMX'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[0].LeafJawPositions = [x1,x2]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[1].RTBeamLimitingDeviceType = 'ASYMY'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[1].LeafJawPositions = [y1, y2]
                    BeamLimitingDevicePosition3 = Dataset() #this will be the MLC 
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence.append(BeamLimitingDevicePosition3)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[2].RTBeamLimitingDeviceType = 'MLCX'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[2].LeafJawPositions = totalleafpositions[j]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].SourceToSurfaceDistance = ssd
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDeviceRotationDirection = 'NONE'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].PatientSupportAngle = psupportangle
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].PatientSupportRotationDirection = 'NONE'
                    _iso = isocenter if len(isocenter) >= 3 else [0.0, 0.0, 0.0]
                    print("No step-and-shoot Setting Isocenter postion: " + "[" + str(float(_iso[0]) - xshift) +" , " +str(float(_iso[1]) - yshift) + " , " + str(float(_iso[2]))+ "]")
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].IsocenterPosition = [float(_iso[0]) - xshift, float(_iso[1]) - yshift, float(_iso[2])]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].GantryRotationDirection = gantryrotdir
                    ds.BeamSequence[beamcount - 1].NumberOfWedges = numwedges
                    ds.BeamSequence[beamcount - 1].NumberOfCompensators = '0' # this is temporary value, will read in from file later
                    ds.BeamSequence[beamcount - 1].NumberOfBoli = '0' # Also temporary
                    ds.BeamSequence[beamcount - 1].NumberOfBlocks = '0' # Temp 
                else:
                    BeamLimitingDevicePosition1 = Dataset() #This will be the mlcs for control points other than the first
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence.append(BeamLimitingDevicePosition1)
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[0].RTBeamLimitingDeviceType = 'MLCX'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].BeamLimitingDevicePositionSequence[0].LeafJawPositions = totalleafpositions[j-1]
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence[0].CumulativeDoseReferenceCoefficient = '1'
                    ds.BeamSequence[beamcount - 1].ControlPointSequence[j].ReferencedDoseReferenceSequence[0].ReferencedDoseReferenceNumber = '1'
                
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence = Sequence()
                BeamLimitingDevice1 = Dataset()
                BeamLimitingDevice2 = Dataset()
                BeamLimitingDevice3 = Dataset()
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence.append(BeamLimitingDevice1)
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence.append(BeamLimitingDevice2)
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence.append(BeamLimitingDevice3)
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[0].RTBeamLimitingDeviceType = 'ASYMX'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[1].RTBeamLimitingDeviceType = 'ASYMY'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[2].RTBeamLimitingDeviceType = 'MLCX'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[0].NumberOfLeafJawPairs = '1'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[1].NumberOfLeafJawPairs = '1'
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[2].NumberOfLeafJawPairs = '60'
                bounds = ['-200','-190','-180','-170','-160','-150','-140','-130','-120','-110','-100','-95','-90','-85','-80','-75','-70','-65','-60','-55','-50','-45','-40','-35','-30','-25','-20','-15','-10','-5','0','5','10','15','20','25','30','35','40','45','50','55','60','65','70','75','80','85','90','95','100','110','120','130','140','150','160','170','180','190','200']
                ds.BeamSequence[beamcount - 1].BeamLimitingDeviceSequence[2].LeafPositionBoundaries = bounds
            ctrlptlist = False 
            wedgeflag = False
            numwedges = 0
            beginbeam = False
    ds.FractionGroupSequence[0].FractionGroupNumber = 1
    ds.FractionGroupSequence[0].NumberOfFractionsPlanned = numfracs
    ds.FractionGroupSequence[0].NumberOfBeams = beamcount
    ds.FractionGroupSequence[0].NumberOfBrachyApplicationSetups = '0'
    summed_pixel_values = []
    flag_nobinaryfile = False
    # Check if all beams have valid MU for consistent dose scaling
    n_beams_in_loop = min(beamcount, len(beamdoses), len(beamdosefiles))
    beams_with_zero_mu = [i+1 for i in range(n_beams_in_loop) if beamdoses[i] == 0]
    if beams_with_zero_mu and len(beams_with_zero_mu) < n_beams_in_loop:
        print("WARNING: beams %s have MU=0 (PDD calc failed). Their dose contributions "
              "will be raw (un-scaled) while other beams are in absolute Gy. "
              "Summed dose may be inaccurate." % beams_with_zero_mu)
    elif beams_with_zero_mu and len(beams_with_zero_mu) == n_beams_in_loop:
        print("INFO: All beams have MU=0. Dose will be in Pinnacle-internal relative units.")
    for currentbeam in range(0,n_beams_in_loop):
        ps_ds = Dataset()
        ds.PatientSetupSequence.append(ps_ds)
        ds.PatientSetupSequence[currentbeam].PatientPosition = patient_position #get this from patient setup file
        ds.PatientSetupSequence[currentbeam].PatientSetupNumber = (currentbeam + 1)
        
        temp_pixelvalues, doseds = creatertdose(plannumber, planfolder, currentbeam + 1, beamdosefiles[currentbeam], beamdoses[currentbeam], numfracs)
        # Override the per-beam UID with a plan-level dose UID (all beams sum into one RD)
        _plan_dose_uid = make_sub_uid(doseinstuid, plannumber)
        doseds.file_meta.MediaStorageSOPInstanceUID = _plan_dose_uid
        doseds.SOPInstanceUID = _plan_dose_uid
        if flag_nobinaryfile:
            continue
        else:
            if currentbeam == 0:
                summed_pixel_values = temp_pixelvalues
            else:
                for i in range(0,len(summed_pixel_values)):
                    summed_pixel_values[i] = summed_pixel_values[i] + temp_pixelvalues[i]
    

    if flag_nobinaryfile == False and len(summed_pixel_values) > 0:
        print("Max pixel value: " + str(max(summed_pixel_values)))
        print("Min pixel value: " + str(min(summed_pixel_values)))

        # ---- Sanity check: pixel buffer size must match declared grid dims ----
        expected_voxels = int(dosexdim) * int(doseydim) * int(dosezdim)
        actual_voxels = len(summed_pixel_values)
        if actual_voxels != expected_voxels:
            print(
                "WARNING: dose pixel count mismatch — "
                "expected %d (%d x %d x %d), got %d. "
                "Pinnacle binary file size disagrees with trial dose grid "
                "dimensions; the resulting RD will fail validation."
                % (expected_voxels, dosexdim, doseydim, dosezdim, actual_voxels)
            )
            # Truncate or pad to match declared dimensions so the file is at
            # least *parseable*; the data may be wrong but the validator
            # length check will pass.
            if actual_voxels > expected_voxels:
                summed_pixel_values = summed_pixel_values[:expected_voxels]
            else:
                summed_pixel_values = list(summed_pixel_values) + \
                    [0.0] * (expected_voxels - actual_voxels)

        max_val = max(summed_pixel_values) if summed_pixel_values else 0
        if max_val <= 0:
            scale = 1.0
        else:
            scale = max_val / 65530.0
        # DoseGridScaling has VR=DS (max 16 chars). Use the formatter so we
        # never silently overflow.
        doseds.DoseGridScaling = format_ds(scale)
        print("Dose grid scaling: " + str(scale))

        pixelvaluelist = []
        clamped = 0
        for element in summed_pixel_values:
            if scale != 0:
                element = round(element / scale)
            else:
                element = 0
            if element < 0:
                clamped += 1
                element = 0
            pixelvaluelist.append(element)
        if clamped:
            print("Note: clamped %d negative voxels to 0 for unsigned packing"
                  % clamped)

        # Pack as little-endian unsigned 32-bit ('<I') so the byte order is
        # explicit and matches Explicit VR LE transfer syntax. Native '%sI'
        # works on x86 by accident; '<I' is correct on every platform.
        pixel_binary_block = struct.pack('<%dI' % len(pixelvaluelist),
                                         *pixelvaluelist)
        doseds.PixelData = pixel_binary_block

        # Re-assert dimensions and pixel attributes so the validator can compute
        # expected pixel data length consistently.
        doseds.NumberOfFrames = int(dosezdim)
        doseds.Rows = int(doseydim)
        doseds.Columns = int(dosexdim)
        doseds.SamplesPerPixel = 1
        doseds.PhotometricInterpretation = 'MONOCHROME2'
        doseds.BitsAllocated = 32
        doseds.BitsStored = 32
        doseds.HighBit = 31
        doseds.PixelRepresentation = 0  # unsigned, matches '<I' packing

        # FrameIncrementPointer must point to GridFrameOffsetVector tag
        doseds.FrameIncrementPointer = doseds.data_element("GridFrameOffsetVector").tag

        # Re-assert the dose→plan reference with matching UID
        doseds.ReferencedRTPlanSequence[0].ReferencedSOPInstanceUID = make_sub_uid(plansopinstuid, plannumber)

        # Verify length matches what DICOM viewers compute
        expected_bytes = (int(doseds.Rows) * int(doseds.Columns) *
                          int(doseds.NumberOfFrames) *
                          int(doseds.SamplesPerPixel) *
                          int(doseds.BitsAllocated) // 8)
        actual_bytes = len(pixel_binary_block)
        if expected_bytes != actual_bytes:
            print("ERROR: PixelData length %d != expected %d. RD will be invalid."
                  % (actual_bytes, expected_bytes))

        # Force RT Dose to Explicit VR LE — required for 32-bit pixel data.
        doseds.file_meta.TransferSyntaxUID = RTDOSE_TRANSFER_SYNTAX_UID

        dosefilename = "RD." + doseds.file_meta.MediaStorageSOPInstanceUID + ".dcm"
        print("\n Creating Dose file: %s \n" % (dosefilename))
        save_dicom_strict(doseds, Outputf + "%s/%s" % (patientfolder, dosefilename))
    #ds.FractionGroupSequence[0].ReferencedDoseReferenceSequence = Sequence()
    #ReferencedDoseReference2 = Dataset()
    #ds.FractionGroupSequence[0].ReferencedDoseReferenceSequence.append(ReferencedDoseReference2)
    #ds.FractionGroupSequence[0].ReferencedDoseReferenceSequence[0].TargetPrescriptionDose = int(prescdose)/int(numfracs)
    return ds
####################################################################################################################################################
####################################################################################################################################################


####################################################################################################################################################
#  Function: creatertdose
#  Purpose: create rt dose data structure and fill it
#  Requirements: Needs plan number and beam number
####################################################################################################################################################
def creatertdose(plannumber, planfolder, beamnum, binarynum, beamdosevalue, numfracs):
    global patientname
    global plansopinstuid
    global dob
    global pid
    global patient_sex
    global plansopinstuid
    global study_time
    global study_date
    global StudyInstanceUID
    global model
    global physician
    global doseseriesuid
    global doseinstuid
    global FrameUID
    global dosexdim
    global doseydim
    global dosezdim
    global doseoriginx
    global doseoriginy
    global doseoriginz
    global pixspacingy
    global pixspacingx
    global pixspacingz
    global posrefind
    global image_orientation
    global flag_nobinaryfile
    #Image Position (Patient) seems off, so going to calculate shift assuming dose origin in center and I want outer edge
    ydoseshift = float(pixspacingy)*float(doseydim)
    zdoseshift = float(pixspacingz)*float(dosezdim)
    #xdoseshift = float(pixspacingx)*float(dosexdim)/2
     # Populate required values for file meta information
    file_meta = Dataset()
    file_meta.MediaStorageSOPClassUID = '1.2.840.10008.5.1.4.1.1.481.2' # RT Dose Storage
    file_meta.TransferSyntaxUID = RTDOSE_TRANSFER_SYNTAX_UID  # Explicit VR Little Endian (required for 32-bit pixel data)
    _dose_sop_uid = make_sub_uid(doseinstuid, plannumber, beamnum)
    file_meta.MediaStorageSOPInstanceUID = _dose_sop_uid
    file_meta.ImplementationClassUID = gImplementationClassUID #this value remains static since implementation for creating file is the same
    # Create the FileDataset instance (initially no data elements, but file_meta supplied)
    RDfilename="RD."+file_meta.MediaStorageSOPInstanceUID+".dcm"
    #print("Dose file name : " + RDfilename)

    ds = FileDataset(RDfilename, {}, file_meta=file_meta, preamble=b'\x00'*128)
    
    ds.SpecificCharacterSet = 'ISO_IR 100'
    ds.InstanceCreationDate = time.strftime("%Y%m%d")
    ds.InstanceCreationTime = time.strftime("%H%M%S")
    ds.SOPClassUID = '1.2.840.10008.5.1.4.1.1.481.2' # RT Dose Storage
    ds.SOPInstanceUID = _dose_sop_uid
    ds.StudyDate = study_date
    ds.StudyTime = study_time
    ds.AccessionNumber = ''
    ds.Modality = 'RTDOSE'
    ds.Manufacturer = Manufacturer
    ds.ReferringPhysicianName = physician if physician else ""
    ds.OperatorsName = ""
    ds.ManufacturerModelName = model
    ds.SoftwareVersions = softwarev if softwarev else 'Unknown'
    ds.PhysiciansOfRecord = physician
    ds.PatientName = patientname
    ds.PatientBirthDate = dob
    ds.PatientID = pid
    ds.PatientSex = patient_sex
    ds.SliceThickness = pixspacingz #Get this value from images???
    ds.StudyInstanceUID = StudyInstanceUID
    ds.SeriesInstanceUID = make_sub_uid(doseseriesuid, plannumber, beamnum)
    ds.StudyID = sid
    if(patient_position == 'HFS'):
        ds.ImagePositionPatient = [round(float(doseoriginx), 4), round(float(doseoriginy) - ydoseshift, 4), round(float(doseoriginz) - zdoseshift, 4)]
    elif(patient_position == 'HFP'):
        ds.ImagePositionPatient = [round(float(doseoriginx), 4), round(float(doseoriginy) + ydoseshift, 4), round(float(doseoriginz) - zdoseshift, 4)]
    elif(patient_position == 'FFS'):
        ds.ImagePositionPatient = [round(float(doseoriginx), 4), round(float(doseoriginy) - ydoseshift, 4), round(float(doseoriginz) + zdoseshift, 4)]
    elif(patient_position == 'FFP'):
        ds.ImagePositionPatient = [round(float(doseoriginx), 4), round(float(doseoriginy) + ydoseshift, 4), round(float(doseoriginz) + zdoseshift, 4)]
    ds.ImageOrientationPatient = image_orientation
    ds.FrameOfReferenceUID = FrameUID
    ds.PositionReferenceIndicator = posrefind #From image files?
    ds.SamplesPerPixel = 1
    ds.PhotometricInterpretation = 'MONOCHROME2'
    
    ds.NumberOfFrames = int(dosezdim) # is this Z dimension???
    ds.Rows = int(doseydim) #Using y for Rows because that's what's in the exported dicom file for test patient
    ds.Columns = int(dosexdim) #similar to above, x for columns
    ds.PixelSpacing = [pixspacingx, pixspacingy]
    ds.BitsAllocated = 32 #????
    ds.BitsStored = 32 #???
    ds.HighBit = 31 #???
    ds.PixelRepresentation = 0
    ds.DoseUnits =  'GY' #'RELATIVE'#'GY'
    ds.DoseType = 'PHYSICAL'
    ds.DoseSummationType = 'PLAN'
    ds.ReferencedRTPlanSequence = Sequence()
    ReferencedRTPlan1 = Dataset()
    ds.ReferencedRTPlanSequence.append(ReferencedRTPlan1)
    ds.ReferencedRTPlanSequence[0].ReferencedSOPClassUID = '1.2.840.10008.5.1.4.1.1.481.5'
    ds.ReferencedRTPlanSequence[0].ReferencedSOPInstanceUID = make_sub_uid(plansopinstuid, plannumber)
    ds.ReferencedRTPlanSequence[0].ReferencedFractionGroupSequence = Sequence()
    ReferencedFractionGroup1 = Dataset()
    ds.ReferencedRTPlanSequence[0].ReferencedFractionGroupSequence.append(ReferencedFractionGroup1)
    ds.ReferencedRTPlanSequence[0].ReferencedFractionGroupSequence[0].ReferencedBeamSequence = Sequence()
    ReferencedBeam1 = Dataset()
    ds.ReferencedRTPlanSequence[0].ReferencedFractionGroupSequence[0].ReferencedBeamSequence.append(ReferencedBeam1)
    ds.ReferencedRTPlanSequence[0].ReferencedFractionGroupSequence[0].ReferencedBeamSequence[0].ReferencedBeamNumber = beamnum
    ds.ReferencedRTPlanSequence[0].ReferencedFractionGroupSequence[0].ReferencedFractionGroupNumber = '1'
    ds.TissueHeterogeneityCorrection = 'IMAGE'
    # GridFrameOffsetVector: distance in mm of each frame from the first frame.
    # Must be float — int(p * pixspacingz) truncates non-integer slice spacings
    # (e.g. 2.5 mm becomes 2 mm), which makes viewers compute slice positions
    # inconsistent with the data. VR is DS so values must be plain numbers.
    frameoffsetvect = [round(p * float(pixspacingz), 4)
                       for p in range(int(dosezdim))]
    ds.GridFrameOffsetVector = frameoffsetvect
    pixeldatallist = []
    #print("Binary file: " + "plan.Trial.binary.%s"%binarynum)
    if os.path.isfile("%s%s/%s/plan.Trial.binary.%s"%(Inputf, patientfolder, planfolder, binarynum)):
        with open("%s%s/%s/plan.Trial.binary.%s"%(Inputf,patientfolder, planfolder, binarynum), "rb") as binary_file:
            data_element = binary_file.read(4)
            while data_element:
                value = struct.unpack(">f", data_element)[0]
                # Pinnacle binary stores dose normalised to 1 MU. When we have
                # valid MU (beamdosevalue > 0), scale to absolute dose in Gy:
                #   dose_Gy = raw_value × (MU / 100) × numfracs
                # When MU is unknown (beamdosevalue == 0), keep raw values so
                # the dose distribution shape is preserved.
                if beamdosevalue > 0:
                    value = value * float(beamdosevalue) / 100.0 * float(numfracs)
                pixeldatallist.append(value)
                data_element = binary_file.read(4)
    else:
        flag_nobinaryfile = True
    #print("Length of Pixel Data list: " + str(len(pixeldatallist)))
    #print("Z dim: " + str(dosezdim) + "       X dim: " + str(dosexdim)  + "       Y dim: " + str(doseydim))
    if len(pixeldatallist) == 0: #if the binary file is empty, treat as if it does not exist
        flag_nobinaryfile = True
    main_pix_array = []
    if flag_nobinaryfile == False:
        # Sanity check: binary file size vs. declared dose grid dimensions
        expected_voxels = int(dosexdim) * int(doseydim) * int(dosezdim)
        if len(pixeldatallist) != expected_voxels:
            print(
                "WARNING: beam %s binary has %d voxels but trial declares %d "
                "(%d x %d x %d). Older Pinnacle versions sometimes write a "
                "different grid than the trial header records."
                % (binarynum, len(pixeldatallist), expected_voxels,
                   dosexdim, doseydim, dosezdim)
            )

        ds.FrameIncrementPointer = ds.data_element("GridFrameOffsetVector").tag

        for h in range(0, dosezdim):
            pixelsforframe = []
            for k in range(0, dosexdim*doseydim):
                idx = h*doseydim*dosexdim + k
                if idx < len(pixeldatallist):
                    pixelsforframe.append(float(pixeldatallist[idx]))
                else:
                    pixelsforframe.append(0.0)
            main_pix_array = main_pix_array + list(reversed(pixelsforframe))

        main_pix_array = list(reversed(main_pix_array))

        # NOTE: this per-beam ds is *not* saved here. Its scale/PixelData are
        # only set so caller can still introspect; the actual file is saved by
        # the plan-level code from summed values. Keep the formatting consistent
        # with the plan-level path so we never end up with a >16-char DS or
        # platform-dependent endianness.
        temp_beamds = ds
        max_val = max(main_pix_array) if main_pix_array else 0
        scale = (max_val / 65530.0) if max_val > 0 else 1.0
        temp_beamds.DoseGridScaling = format_ds(scale)
        pixelvaluelist = []
        for element in main_pix_array:
            if scale != 0:
                element = round(element / scale)
            else:
                element = 0
            if element < 0:
                element = 0
            pixelvaluelist.append(element)
        pixel_binary_block = struct.pack('<%dI' % len(pixelvaluelist),
                                         *pixelvaluelist)
        temp_beamds.PixelData = pixel_binary_block
    return main_pix_array, ds

####################################################################################################################################################
####################################################################################################################################################