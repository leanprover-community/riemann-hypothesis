module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdLOfZetaUr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfVanishOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.UnramifiedZeta.ZetaUr
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

private theorem sphAt_tw {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ι : Qbar l ≃+* ℂ} {e : ℕ} {W : R2 Ω l}
    (h : SphAt ι e W) {N : ℕ} {θ : G ℚ Ω →* (Qbar l)ˣ} (hN : 1 ≤ N) (hθ : KillsMu N θ) : SphAt ι e (Af.tw W θ) := by
  intro M φ hM hφ
  rw [TwDet.tw_tw]
  exact h (M * N) (φ * θ) (Nat.mul_pos hM hN)
    (TwDet.killsMu_mul (TwDet.killsMu_dvd hφ (dvd_mul_right M N)) (TwDet.killsMu_dvd hθ (dvd_mul_left N M)))

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twoS :
    GlobalTheory.Mem.LiteralAutomorphy.LitCoh → SrcS → KatoTwoS := by
  intro hC hSrc l _ Ω _ _ _ K _ _ _ e N θ ψ W u ι f hf hS
  have hV : VanishOrdL := GlobalTheory.Ord2.vanishOrdL_of_zetaUr hC Final.zetaUr
  obtain ⟨hdt, ha⟩ := u.adm hf
  have h1 : Af.tw W 1 = W := by
    ext s i j
    change mat (Af.tw W 1) s i j = mat W s i j
    rw [TwDet.tw_coe]
    simp
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact hV l u.l_odd Ω ι e u.e_pos W ha (hSrc l Ω ι e W u.l_odd u.e_pos ha hS)
  · rw [← hdt]
    obtain ⟨M, hM, hMk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (TwDet.ker_open ha.cont ha.det2)
      (Abelianization.commutator_subset_ker (dt W))
    have ha' := admissible_twist_by_det l Ω ι e W ha
    exact hV l u.l_odd Ω ι e u.e_pos _ ha'
      (hSrc l Ω ι e _ u.l_odd u.e_pos ha' (sphAt_tw hS hM fun s hs => hMk s hs))
