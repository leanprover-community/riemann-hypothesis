module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

private theorem mem_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {s : G F Ω}
    (h : ∀ x, s x ∈ A ↔ x ∈ A) : s ∈ Dec (F := F) A := by
  open Pointwise in
  rw [ReciprocityTheory.Gal.mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have key := h (s⁻¹ • x)
  have e : s (s⁻¹ • x) = x := ReciprocityTheory.Gal.mul_inv_apply x
  rw [e] at key
  exact key.symm

end UpperTheory.V.Keep

theorem UpperTheory.V.Keep.unlL :
    UpperTheory.V.Keep.UnlL := by
  intro Ω _ _ _ l _ c D T hD ho r h w hw A hA
  have hl : A.valuation (l : Ω) < 1 := by
    have h' := (hA ((l : ℕ) : 𝓞 T.L)).2 hw
    simpa using h'
  obtain ⟨κ, hκ, hne⟩ := h A hl
  let ρ : ↥(Dec (F := T.L) A) →* ↥(Dec (F := T.F) A) :=
    ((resLe T.F_le).comp (Dec (F := T.L) A).subtype).codRestrict _ fun s =>
      UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x
  have hρ : Function.Surjective ρ := by
    intro s
    have hd : resQ T.F s.1 ∈ Dec (F := ℚ) A := UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x
    have hK : resQ T.F s.1 ∈ T.K.fixingSubgroup := ho.split l hD.l_mem A hl hd
    have hF : resQ T.F s.1 ∈ T.F.fixingSubgroup := fun x => s.1.commutes x
    have hLf : resQ T.F s.1 ∈ T.L.fixingSubgroup := by
      rw [T.hL, IntermediateField.fixingSubgroup_sup]
      exact ⟨hF, hK⟩
    let t : G T.L Ω := AlgEquiv.ofRingEquiv (f := s.1.toRingEquiv) fun x => hLf x
    refine ⟨⟨t, UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x⟩, Subtype.ext (AlgEquiv.ext fun x => rfl)⟩
  refine ⟨fun i => (κ i).comp ρ, ?_, fun i j e => hne i j (MonoidHom.ext fun s => ?_)⟩
  · obtain ⟨g, hg⟩ := hκ.flag
    exact ⟨g, fun s => hg (ρ s)⟩
  · obtain ⟨t, rfl⟩ := hρ s
    exact DFunLike.congr_fun e t
