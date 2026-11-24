module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE

@[expose] public section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section
namespace GlobalTheory.RealWeilFinFix

theorem actOF_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (g : GAF σ JS) (h : GAF σ JT),
      g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS → h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT → ∀ u : WOF F E nS nT, u.map (infPartF F E) = 0 →
        actOF σ JS JT g h u = u := by
  intro F E _ _ _ _ _ σ nS nT JS JT g h hg hh u hu
  have h1 : (mtF σ JT h).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  have h2 : (mtF σ JS g⁻¹).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h3 : (actOF σ JS JT g h u).map (finPartF F E) = u.map (finPartF F E) := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : (actOF σ JS JT g h u).map (infPartF F E) = u.map (infPartF F E) := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]
  ext i j
  have k3 : finPartF F E (actOF σ JS JT g h u i j) = finPartF F E (u i j) := congrFun (congrFun h3 i) j
  have k4 : infPartF F E (actOF σ JS JT g h u i j) = infPartF F E (u i j) := congrFun (congrFun h4 i) j
  rw [← Formalism.L2.Fam.ThC.pairE_eta (actOF σ JS JT g h u i j), ← Formalism.L2.Fam.ThC.pairE_eta (u i j)]
  exact congrArg₂ Formalism.L2.Fam.ThC.pairE k4 k3

end GlobalTheory.RealWeilFinFix
