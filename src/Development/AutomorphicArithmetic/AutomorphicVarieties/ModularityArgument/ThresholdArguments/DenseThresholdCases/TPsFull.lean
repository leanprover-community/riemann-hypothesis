module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SphUntw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdCharIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Desc.W.principal_series_full_statement : _root_.UpperTheory.V.Z.Desc.W.PsFullAlt := by
  intro P L Ω _ _ _ _ _ l _ ι n w A h a ha τ ω hh ψ ph hs hω hp hinj
  have hv := fun i => ((Loc.ordCharIff P.aut.art h ι a ha (hh i) (ψ i)).2 (ω i) (hω i) (ph i)).1 (hp i)
  have key : ∀ i j, (∀ σ : Ine (F := L) A, ω i (a (ineIncl h σ)) = ω j (a (ineIncl h σ))) → i = j := fun i j e =>
    hinj (MonoidHom.ext fun σ => Units.ext (ι.injective (by rw [hv, hv, e])))
  refine (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient P _ n ω (fun i => (hω i).smooth) fun i j hij => ⟨fun e => hij (key i j fun σ => by rw [e]),
    fun e => hij (key i j fun σ => ?_)⟩).2 _ τ.ρ τ.irred hs
  have h1 := DFunLike.congr_fun (ha.absPow_comp 1) (ineIncl h σ)
  rw [Complex.ofReal_one, MonoidHom.comp_apply, GlobalTheory.WeilDeligne.unrChar_apply, deg_ineIncl] at h1
  rw [e, MonoidHom.mul_apply, h1]
  simp
end
