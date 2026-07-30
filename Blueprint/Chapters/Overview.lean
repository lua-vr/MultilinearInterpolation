import Verso
import VersoManual
import VersoBlueprint
import Blueprint.Commands
import Blueprint.Bibliography

import MultilinearInterpolation

open Verso.Genre Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Overview" =>
%%%
htmlSplit := .never
%%%

Broadly speaking, we want to formalize a version of interpolation for {bpref "MultisubadditiveMap"}[multisubadditive]
operators that starts with a set of points where the operator is known to have restricted weak type,
and concludes that it has strong type in the interior of the convex hull of the points. For that,
we use abstract $`K`-theory and the results in {citet janson}[] to get a general result stated
in terms of abstract interpolation spaces, and then use isomorphisms between the abstract
interpolation spaces and Lorentz spaces to transport that result to Lorentz spaces.

More concretely, fix a finite index set $`ι`, a {bpref "MultisubadditiveMap"}[multisubadditive]
operator $`T`, {bpref "EQuasinorm.Couple"}[couples] of {bpref "EQuasinorm"}[quasinorms] $`A_i` for
$`i ∈ ι` and an output
quasinorm couple $`B`. We are interested in knowing for which values of the parameters
$`θ_0, \theta_i \in [0,1]` and $`q_0, q_i ∈ (0, ∞]` for $`i ∈ ι` the operator $`T` is
{bpref "MultisubadditiveMap.IsBoundedFor"}[bounded]
as an operator between the $`K`-{bpref "EQuasinorm.KMethod"}[interpolation spaces]
$$`T : \prod_{i ∈ ι}(A_i)_{θ_i,p_i} → (B)_{θ_0,p_0}.`
It is known (see an example in {citet janson}[]) that without further assumptions, we have a
restriction
$$`\frac{1}{q_0} ≤ ∑_i \frac{1}{q_i}`
and the output parameter $`θ_0` must depend linearly on the parameters $`\theta_i`, in the
sense that
$$`\theta_0 = α_0 + ∑_i α_i θ_i`
for some choice of coefficients $`(α_i)_{i ∈ ι}` and $`α_0`. In particular, if we start with
$`|ι|+1` linearly independent combinations of $`θ_0` and $`(θ_i)_i` for which the operator is known
to be bounded, then the coefficients uniquely determined.


{citet janson}[] defines a set

{blueprint_node "Ω"}

They proceed to show that the set $`\Omega` is convex.

{blueprint_node "convex_Ω"}

As remarked in the statement above, this still does not handle particular choices of $`q_i`s, which
is necessary for strong-type bounds, where we want the $`p` and $`q` of the Lorentz space $`L_{p,q}`
to be the same. This is finally handled in their Theorem 2 below.

{blueprint_node "isBoundedOn_of_mem_interior_Ω"}

There are three important caveats, and they will be addressed in the sections below. First, we must
relate the abstract statement above with the concrete Lorentz spaces.
Second, the proofs in {citet janson}[] are written for seminorms (a quasinorm with subadditivity
constant `1`), and the adaptation to quasinorms requires an extra step. And finally, the proofs in
the paper assume that we work with all the different norms inside the restricted spaces given by the
{bpref "EQuasinorm.instMin"}[intersection] of the elements of the couples, and then have the
conclusion extended to the whole space. This is generally possible to do in $`L_{p,q}` for $`q ≠ ∞`
because the intersections contain simple functions of finite integral, which are dense.

# From restricted weak type to strong type in the interior

To get the result about restricted weak type and strong type mentioned in the introduction, we make
use of the following result.

{blueprint_node "EQuasinorm.eLorentz_equiv_kMethod_of_neq"}

This is a recipe for

# Dealing with quasinorms

# Extending from the intersection

I am choosing not to write this section now, because I am not sure of its necessity.
