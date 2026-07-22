import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Blueprint.Chapters.EQuasinorm
import Blueprint.Chapters.Janson
import Blueprint.Chapters.KMethod
import Blueprint.Bibliography

open Verso.Genre Manual Informal Bibliography

open Blueprint.Chapters

#doc (Manual) "Multilinear interpolation" =>

Note: unfortunately, `verso-blueprint` is largely vibe-coded and does not work
as well as I would like. The web style of its components is not very formal and
it does not emit proper $`\LaTeX` for the theorems and similar constructs. I am
still using it as a place to make informal comments that do not belong in the
Lean files, because it seemed to be the easiest option to integrate with the
project and it has the benefit of being written in Lean, so hacking it is
easier for me than the alternatives. These difficulties may be improved in the
future.

{include 0 EQuasinorm}
{include 0 KMethod}
{include 0 Janson}

{blueprint_bibliography}
{blueprint_graph}
{blueprint_summary}
