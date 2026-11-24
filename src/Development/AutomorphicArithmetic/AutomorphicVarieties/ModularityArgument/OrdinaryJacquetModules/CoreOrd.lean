module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.OrdScal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PartPt
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord



theorem UpperTheory.V.Z.Ord.coreOrd :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → CoreOrd := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι P hP a K _ _ D ψ hU lam hlam y hy
  let x : A →ₐ[c.O] Qbar l := y.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  have hx : y.toRingHom.comp (algebraMap A _) = x.toRingHom := rfl
  rw [hx] at hy
  obtain ⟨d, ξ, c0, sp, hsp⟩ := UpperTheory.V.Hi.spec L Ω l n c H hA A θ hθ ι x lam hy
  obtain ⟨Y, F, hY, hF0, hF, hop⟩ :=
    UpperTheory.V.Z.Ord.partPt hL L Ω l n c H hA A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K y hx
  obtain ⟨hD, hch⟩ := UpperTheory.V.Hi.coreEig hL L Ω l n c H hA A θ hθ ι a K D ψ hU y lam d ξ Y F hF.1 hF0
    fun w j => hop _
  refine ⟨d, ξ, Y, hY, hD, fun v => ?_⟩
  have hle : H.OrdAt θ ι x.toRingHom lam ξ K c0 ≤ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    unfold HSet.OrdAt
    exact iSup_le fun _ => inf_le_left
  have hC : F ∈ Y.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K c0 := ⟨hF.1, hle hF.2⟩
  have hne : ∀ j : Fin n, ι (y (H.gen θ a K (.inr (v, j)))) ≠ 0 := fun j => by
    obtain ⟨s, hs⟩ := (hA.art_spec v).surj (unif _)
    rw [← hU.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs]
    exact (map_ne_zero ι).2 ((Units.isUnit _).map y).ne_zero
  obtain ⟨ω, hsm, hPS, hinv, hb⟩ := UpperTheory.V.Z.Ord.ordScal hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp
    Y K c0 le_rfl F hC hF0 v (fun j => ι (y (H.gen θ a K (.inr (v, j))))) fun j => ⟨hne j, hop _⟩
  exact ⟨ω, hPS, hch v ω hsm hinv hb⟩
