module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfTailStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousZlSmulStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowInclRSmulMemStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapPiContinuousCoordStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem continuous_io_smul_of {O RA RW M : Type} [CommRing O] [TopologicalSpace O] [CommRing RA]
    [Algebra O RA] [CommRing RW] [Algebra O RW] [AddCommGroup M] [Module RW M] [Module O M]
    [IsScalarTower O RW M] [TopologicalSpace M] [IsTopologicalAddGroup M] {n : ℕ}
    (io : LetA O n →ₐ[O] RA) (inc : RA →ₐ[O] RW) (y : M) (πA : RA) (hπ : io letπ = πA)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ z : RA, inc (πA ^ k * z) • y ∈ U)
    (hlin : ∀ f : (ZMod n → O) →ₗ[O] M, Continuous f) :
    Continuous fun a : LetA O n => inc (io a) • y := by
  let Φ : LetA O n →+ M :=
    { toFun := fun a => inc (io a) • y
      map_zero' := by simp only [map_zero, zero_smul]
      map_add' := fun a c => by simp only [map_add, add_smul] }
  refine GlobalTheory.T.continuous_of_tail_small_of_monomial_continuous Φ ?_ ?_
  · intro U hU
    obtain ⟨k, hk⟩ := hsmall U hU
    refine ⟨k, fun r => ?_⟩
    have hΦ : Φ (letπ ^ k * r) = inc (πA ^ k * io r) • y := by
      show inc (io (letπ ^ k * r)) • y = _
      rw [map_mul, map_pow, hπ]
    rw [hΦ]
    exact hk _
  · intro j
    let f : (ZMod n → O) →ₗ[O] M :=
      { toFun := fun c => inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y)
        map_add' := fun c c' => by
          have : (fun i => PowerSeries.C ((c + c') i)) =
              (fun i => PowerSeries.C (c i)) + fun i => PowerSeries.C (c' i) := by
            funext i; exact map_add PowerSeries.C (c i) (c' i)
          simp only [this, map_add (f := _), add_smul]
        map_smul' := fun o c => by
          have : (fun i => PowerSeries.C ((o • c) i)) = o • (fun i => PowerSeries.C (c i)) := by
            funext i
            simp only [Pi.smul_apply, smul_eq_mul, PowerSeries.smul_eq_C_mul, map_mul]
          simp only [this, map_smul, smul_assoc, RingHom.id_apply] }
    refine (hlin f).congr fun c => ?_
    have hc : (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j : LetA O n) =
        (fun i => PowerSeries.C (c i)) * letπ ^ j := by
      funext i; rw [Pi.mul_apply, Pi.pow_apply]; rfl
    show inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y) =
      inc (io (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) • y
    rw [hc, map_mul, map_mul, mul_smul, map_pow, map_pow]

end GlobalTheory.WeakClosed

namespace GlobalTheory.WeakClosed

theorem isTopologicalAddGroup_twTop {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ}
    (b : LatB T d) : letI := twTop T b; IsTopologicalAddGroup (TW (RW LL) T) := by
  let := cbValued l
  let := zlMod T
  have := zlTower T
  let : TopologicalSpace (WCb l) := wTop l
  let : TopologicalSpace (TW (RW LL) T) := twTop T b
  have : IsTopologicalRing (Cb l) := inferInstance
  have : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  exact Topology.IsInducing.isTopologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩

theorem finrank_maxUnramifiedSubfield_pos {l : ℕ} [Fact l.Prime] (K : FinExt l) : 0 < Module.finrank ℚ_[l] ↥(K0 K) := by
  have hle : K0 K ≤ K.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] (K0 K) :=
    let := K.2
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  exact Module.finrank_pos

-- Resolve the tensor-product actions while the scalar rings are still abstract.
private theorem tensorProduct_left_scalarTower {O R N : Type} [CommRing O] [CommRing R]
    [Algebra O R] [AddCommGroup N] [Module O N] : IsScalarTower O R (R ⊗[O] N) :=
  TensorProduct.isScalarTower_left

theorem continuous_inclR_io_smul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL) {d e : ℕ} (b : LatB T d) (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) (y : TW (RW LL) T), letI := twTop T b; letI := aTop (K := K) bO; Continuous fun a : AA K LL => inclR LL (E.tie.io a) • y := by
  intro l hl P AI K s LL h W E T d e b bO y
  let algA : Algebra ↥(OL LL) (RA LL) :=
    Algebra.TensorProduct.leftAlgebra (R := ℤ_[l]) (A := ↥(OL LL)) (B := Ainf l)
  let algW : Algebra ↥(OL LL) (RW LL) :=
    Algebra.TensorProduct.leftAlgebra (R := ℤ_[l]) (A := ↥(OL LL)) (B := WCb l)
  let modW : Module ↥(OL LL) (RW LL) := Algebra.toModule
  let modSelf : Module (RW LL) (RW LL) := Semiring.toModule
  let modO : Module ↥(OL LL) (TW (RW LL) T) :=
    TensorProduct.instModule (R := ↥(OL LL)) (M := RW LL) (N := ↥T.L.T)
  let modRW : Module (RW LL) (TW (RW LL) T) :=
    TensorProduct.leftModule (R := ↥(OL LL)) (R'' := RW LL) (M := RW LL) (N := ↥T.L.T)
  let tT := twTop T b
  let tO := oTop bO
  have ht := isTopologicalAddGroup_twTop T b
  have hn : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨(finrank_maxUnramifiedSubfield_pos K).ne'⟩
  have hTower := @tensorProduct_left_scalarTower ↥(OL LL) (RW LL) ↥T.L.T _ _ algW _ _
  have hlin := @GlobalTheory.T.continuous_linearMap_pi_of_continuous_coord l hl
    ↥(OL LL) (TW (RW LL) T) (ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    _ _ (ZMod.fintype _) _ modO tT ht e bO (GlobalTheory.T.continuous_padicInt_smul_latB T b)
  exact @continuous_io_smul_of ↥(OL LL) (RA LL) (RW LL) (TW (RW LL) T)
    _ tO _ algA _ algW _ modRW modO hTower tT ht _
    E.tie.io (inclR LL) y _ E.tie.io_π (GlobalTheory.T.exists_pow_inclR_smul_mem' AI s T b y) hlin

end GlobalTheory.WeakClosed
