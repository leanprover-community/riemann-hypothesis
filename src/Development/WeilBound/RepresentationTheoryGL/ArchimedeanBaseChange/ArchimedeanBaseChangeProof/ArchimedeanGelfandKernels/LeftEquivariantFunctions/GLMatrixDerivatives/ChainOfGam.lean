module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfLoc

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Gam

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem iteratedDeriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (k : ℕ)
    (t : ℝ) : iteratedDeriv k (fun s => A (φ s)) t = A (iteratedDeriv k φ t) := by
  have h := (A.restrictScalars ℝ).iteratedFDeriv_comp_left (f := φ) (x := t) (i := k)
  have h2 := congrArg (fun L => L (fun _ : Fin k => (1 : ℝ))) h
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h2
  exact h2

theorem deriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (t : ℝ) :
    deriv (fun s => A (φ s)) t = A (deriv φ t) := by
  have := iteratedDeriv_equiv A φ 1 t
  simpa only [iteratedDeriv_one] using this

theorem wave_equiv (E : KMod n) (A : E.V ≃L[ℂ] E.V) (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v))
    (u : ℝ → Mat n → E.V) (hu : IsWave E u) : IsWave E fun t x => A (u t x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn h1
  · intro t
    refine ⟨(A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn (h2 t).1, ?_⟩
    intro g hg k
    simp only
    rw [(h2 t).2 g hg k, hA]
  · intro t g hg
    rw [iteratedDeriv_equiv A (fun s => u s g) 2 t, h3 t g hg, om_equiv]
  · intro g hg
    rw [deriv_equiv A (fun s => u s g) 0, h4 g hg, map_zero]

theorem act_equiv (hWE : WaveEx) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (A : E.V ≃L[ℂ] E.V)
    (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v)) (w : List (Bool × ℕ)) (g : ℝ → ℝ)
    (ks : Mat n → (E.V →L[ℂ] E.V)) (hks : IsKer μ E w g ks) (f : Mat n → E.V) (hf : f ∈ CE E) :
    act μ E ks (fun x => A (f x)) 1 = A (act μ E ks f 1) := by
  obtain ⟨u, hu, hu0⟩ := hWE n E f hf
  have hAu := wave_equiv E A hA u hu
  have hone : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have key : ∀ F F' : Mat n → E.V, Set.EqOn F F' (GLs n) → act μ E ks F 1 = act μ E ks F' 1 := by
    intro F F' h
    unfold act
    congr 1
    funext y
    rw [h]
    simp only [GLs, Set.mem_setOf_eq, one_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  rw [key (fun x => A (f x)) (fun x => A (u 0 x)) (fun x hx => by simp only [hu0 x hx]),
    key f (u 0) (fun x hx => (hu0 x hx).symm),
    hks.2.2.2 _ hAu 1 hone, hks.2.2.2 _ hu 1 hone]
  refine Eq.trans ?_ (congrFun (zop_equiv A w _) 1)
  congr 2
  funext x'
  rw [← A.integral_comp_comm]
  congr 1
  funext t
  exact ((A : E.V →L[ℂ] E.V).map_smul_of_tower (g t) (u t x')).symm

end PositivityTheory.RgBcC.LfSt.ChainPf.Gam
