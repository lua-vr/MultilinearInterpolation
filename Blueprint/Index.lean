import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import MultilinearInterpolation
import Blueprint.Chapters.EQuasinorm
import Blueprint.Chapters.Overview
import Blueprint.Chapters.Janson
import Blueprint.Chapters.KMethod
import Blueprint.Chapters.Multisubadditive
import Blueprint.Bibliography

open Verso.Genre Manual Informal Bibliography

open Blueprint.Chapters

#doc (Manual) "Multilinear interpolation" =>

The main goal of this blueprint is to make the formalization understandable by both contributors and
interested readers. In particular, it is meant to give an overview of the whole proof while also
explaining particular choices made during the formalization.

It aims to not contain LLM-generated text.

{include 0 Overview}
{include 0 EQuasinorm}
{include 0 Multisubadditive}
{includeBlueprintModule MultilinearInterpolation.AokiRolewicz}
{include 0 KMethod}
{includeBlueprintModule MultilinearInterpolation.Janson (title := "Interpolation of multi-linear operators")}

# Notes and TODOs
%%%
htmlSplit := .never
%%%

## `AddGroup` versus `AddMonoid`
%%%
tag := "group-or-monoid"
%%%

It's not clear if at some point there will be need to work with additive groups.
There is one place where they seem necessary:

1. If we want to put a topology (or more broadly, an uniform structure)
   induced by the quasinorm, we would need to use the distance `d(x,y) = ‖x -
   y‖`. However, this may not be necessary for the main results, and it may be
   assumed only in the constructor for the topology. In such cases, it is
   important to have the extra assumption that `‖-x‖ = ‖x‖` to define the
   uniformity.

In case we require an {InlineLean.name}`AddGroup` for the `EQuasinorm`
definition, we will also need an `ESeminormedAddGroup` class for stating the
results in `ELorentz`, because they depend on the class `ESeminormedAddMonoid`.

## Verso-blueprint

`verso-blueprint` is developed using LLMs and despite working well in some aspects, does not as I
would like in others. The web style of its components is not very formal and it does not emit proper
$`\LaTeX` for the theorems and similar constructs. I chose to make some patches to its style in the
module `Blueprint.StylePatches`, and I used an LLM to fight those issues introduced by some LLM.

Despite that, it seemed to be the easiest option to integrate with the project
and it has the benefit of being written in Lean, so hacking it is easier for me
than the alternatives.

Some feature requests:
- Add a `details` spoiler in definitions and proofs showing the bodies of the declarations
   (preferably with the Verso hovers :).

{blueprint_bibliography}
{blueprint_graph}
{blueprint_summary}
