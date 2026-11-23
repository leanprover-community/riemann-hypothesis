module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapPiEqOfMapAddHaarEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

def matrixColumns (R : Type) [AddCommGroup R] (n m : ℕ) :
    Matrix (Fin n) (Fin m) R ≃+ (Fin m → Fin n → R) where
  toFun x j i := x i j
  invFun y := Matrix.of fun i j => y j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem map_mul_left_eq_of_mulVec (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    (n m : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ ν : Measure (Fin n → R), ν.IsAddHaarMeasure → ν.map A.mulVecLin = ν)
    (μ : @Measure (Matrix (Fin n) (Fin m) R) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (Matrix (Fin n) (Fin m) R) _ _ (borel _) μ) :
    @Measure.map _ _ (borel _) (borel _) (fun x : Matrix (Fin n) (Fin m) R => A * x) μ = μ := by
  letI mM : MeasurableSpace (Matrix (Fin n) (Fin m) R) := borel _
  haveI bM : BorelSpace (Matrix (Fin n) (Fin m) R) := ⟨rfl⟩
  letI mP : MeasurableSpace (Fin m → Fin n → R) := borel _
  haveI bP : BorelSpace (Fin m → Fin n → R) := ⟨rfl⟩
  let e := matrixColumns R n m
  have he : Continuous e := continuous_pi fun j => continuous_pi fun i =>
    (continuous_apply j).comp (continuous_apply i)
  have hes : Continuous e.symm := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (continuous_apply j)
  let φ : (Fin n → R) →+ (Fin n → R) := A.mulVecLin.toAddMonoidHom
  have hφ : Continuous φ := Continuous.matrix_mulVec continuous_const continuous_id
  haveI hν : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have key := map_pi_eq_of_map_addHaar_eq (Fin n → R) φ hφ hA m (μ.map e) hν
  have hΦ : Continuous (fun (x : Fin m → Fin n → R) i => φ (x i)) :=
    continuous_pi fun i => hφ.comp (continuous_apply i)
  have hfac : (fun x : Matrix (Fin n) (Fin m) R => A * x) =
      e.symm ∘ (fun (x : Fin m → Fin n → R) i => φ (x i)) ∘ e := by
    funext x
    ext i j
    exact Matrix.mul_apply
  rw [hfac]
  calc μ.map (e.symm ∘ (fun (x : Fin m → Fin n → R) i => φ (x i)) ∘ e)
      = ((μ.map e).map (fun (x : Fin m → Fin n → R) i => φ (x i))).map e.symm := by
        rw [Measure.map_map hΦ.measurable he.measurable, Measure.map_map hes.measurable (hΦ.comp he).measurable]
    _ = (μ.map e).map e.symm := by rw [key]
    _ = μ := by
        rw [Measure.map_map hes.measurable he.measurable]
        have : (e.symm ∘ e : Matrix (Fin n) (Fin m) R → _) = id := by
          funext x; simp
        rw [this, Measure.map_id]

theorem map_mt_mul_eq : ∀ (D : D7) (V : HSp D) (m : ℕ) (g : GA D V) (μ : Measure (Mx D V.rank m)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D V.rank m => (HMul.hMul (mt V g) (x : Matrix (Fin V.rank) (Fin m) (AE D)) : Mx D V.rank m)) = μ := by
  intro D V m g μ hμ
  refine map_mul_left_eq_of_mulVec (AE D) V.rank m (mt V g) ?_ μ hμ
  intro ν hν
  exact PI.VolSemiDirect.W.Cj.unipotent_modulus_holds _ _ D.sp.cm.sig (GlobalTheory.Mem.VolExists.isCMExt D.sp.cm) V.rank V.gram (GlobalTheory.Mem.VolExists.isHermND D.sp.cm V) g ν hν

end GlobalTheory
