module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneSmulAdr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem chi_adrU_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (τ : ℝ) :
    haveI := d.cm.1
    (d.χ (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : ℂ) = 1 := by
  haveI := d.cm.1
  haveI : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : StrongRankCondition (AF F) := commRing_strongRankCondition _
  have hfr : Module.finrank (AF F) (AE F E) = 2 := by
    rw [Module.finrank_baseChange]; exact d.cm.2.2.1
  have hmem : adrU w τ ∈ (Units.map (Algebra.norm (AF F) : AE F E →* AF F)).range := by
    refine ⟨Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w (τ / 2)), Units.ext ?_⟩
    show Algebra.norm (AF F) (algebraMap (AF F) (AE F E) (adr w (Real.exp (τ / 2)))) = adr w (Real.exp τ)
    rw [Algebra.norm_algebraMap, hfr, sq, adr_mul, ← Real.exp_add, add_halves]
  have := d.ok.res (adrU w τ)
  rw [if_pos (Subgroup.mem_sup_right hmem)] at this
  exact this
end PositivityTheory.SiegelWeilFormula.AStep
end
end
