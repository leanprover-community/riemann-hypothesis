module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ExistsNeZeroOfMap
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eta_sign_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) {ε : ℤˣ}
    (hb : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    σ η = -(((ε : ℤ) : E)) * η := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he := frame_sign hσ d.ok.hn d.Y.J (-1) (fun i j => by rw [hY, neg_one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 1
      (by rw [one_smul]; exact ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.herm] at h
    rw [he, neg_neg, one_mul]
    exact mul_right_cancel₀ hij h
  · have he := frame_sign hσ d.ok.hn d.Y.J 1 (fun i j => by rw [hY, one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 Complex.I (ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.skew] at h
    rw [he, neg_one_mul]
    apply mul_right_cancel₀ hij
    linear_combination -h
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
