import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Blueprint.Chapters.EQuasinorm
import Blueprint.Chapters.Janson
import Blueprint.Chapters.KMethod
import Blueprint.Chapters.Multisubadditive
import Blueprint.Bibliography

open Verso.Genre Manual Informal Bibliography

open Blueprint.Chapters

#doc (Manual) "Multilinear interpolation" =>

{include 0 EQuasinorm}
{include 0 Multisubadditive}
{include 0 KMethod}
{includeBlueprintModule MultilinearInterpolation.Janson (title := "Interpolation of multi-linear operators")}

# Notes
%%%
htmlSplit := .never
%%%

## `AddGroup` versus `AddMonoid`
%%%
tag := "group-or-monoid"
%%%

It's not clear to me if at some point we will have to work with additive groups.
There is one place where they seem necessary:

1. If we want to put a topology (or more broadly, an uniform structure)
   on the space. However, this may not be necessary for the main results, and it
   may be assumed only in the constructor for the topology. In such cases, it is
   important to have the extra assumption that `‖-x‖ = ‖x‖` to define the
   uniformity.

In case we require an {InlineLean.name}`AddGroup` for the `EQuasinorm`
definition, we will also need an `ESeminormedAddGroup` class for stating the
results in `ELorentz`, because they depend on the class `ESeminormedAddMonoid`.

## Verso-blueprint

`verso-blueprint` is developed using AI and does not work as well as I would
like in some aspects. The web style of its components is not very formal and it
does not emit proper $`\LaTeX` for the theorems and similar constructs. I chose
to make some patches to its style in the module `Blueprint.StylePatches`, also
using AI.

Despite that, it seemed to be the easiest option to integrate with the project
and it has the benefit of being written in Lean, so hacking it is easier for me
than the alternatives. These difficulties may be improved in the future.

{blueprint_bibliography}
{blueprint_graph}
{blueprint_summary}
