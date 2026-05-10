"""
pinnacle_tar_dicom — Pinnacle tar archive to DICOM converter.

Handles older Pinnacle TPS versions (v8.x–v9.x) that lack pre-built
DICOM image folders and use legacy text-based data formats.

Usage as a library:
    from pinnacle_tar_dicom import convert

    convert(
        input_base="/path/to/extracted/",   # parent of Patient_XXXXX folder
        output_base="/path/to/output/",     # where DICOM files are written
        patient_folder="Patient_XXXXX",     # the patient directory name
    )
"""

from .createDICOM import main as convert

__all__ = ["convert"]