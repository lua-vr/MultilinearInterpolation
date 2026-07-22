import VersoManual
import VersoBlueprint.PreviewManifest
import Blueprint.Index
import Blueprint.StylePatches

open Verso Doc Output
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc Blueprint.Index)
    args
    (extensionImpls := by exact extension_impls%)
    (config := { extraHead := fontHead ++ manualBoxHead })
