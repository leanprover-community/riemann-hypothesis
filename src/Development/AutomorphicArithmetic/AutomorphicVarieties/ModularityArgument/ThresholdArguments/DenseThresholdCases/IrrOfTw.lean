module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
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




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness
private theorem irr_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (h : IsIrr (tw r φ)) : IsIrr r := by
  obtain ⟨hne, -, hmin⟩ := h
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun U _ hU => hmin U le_top fun s v hv => ?_⟩
  have e : (tw r φ s : Matrix (Fin n) (Fin n) k).mulVec v =
      (φ s : k) • (r s : Matrix (Fin n) (Fin n) k).mulVec v := by
    rw [tw_val, Matrix.smul_mulVec]
  rw [e]
  exact U.smul_mem _ (hU s v hv)
private theorem comp_tw {Γ Δ k : Type} [Group Γ] [Group Δ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (f : Δ →* Γ) : (tw r φ).comp f = tw (r.comp f) (φ.comp f) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  simp only [MonoidHom.comp_apply, tw_val]
private theorem open_ker {K Ω C : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [Algebra ℚ K] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] [Group C] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* C}
    (hφ : KillsMu M φ) :
    IsOpen ((φ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)).ker : Set (G K Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := K) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ _ fun ζ hζ => hs ζ hζ
end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness
open UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twWit_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Z.Win.AIsoTwAlt → TwWit := by
  intro P hI l _ Ω _ _ _ ι n W M φ hM hφ hW K _ _ _ _ _ _ hK hirr
  haveI : Algebra.IsAlgebraic ℚ K := inferInstance
  haveI : IsAlgClosure K Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, (IsAlgClosure.isAlgebraic (R := ℚ) (K := Ω)).tower_top K⟩
  rw [comp_tw] at hirr ⊢
  have hW' := hW K hK (irr_of_tw _ _ hirr)
  have hs := (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results P K Ω l ι).1 0 (φ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))
    (open_ker hM hφ)
  rw [zpow_zero, one_mul] at hs
  obtain ⟨hc, art, χ, a, h⟩ := hs
  exact (hI P K Ω l ι n _ hW').2 _ ⟨χ, hc, art, a, h⟩
end
