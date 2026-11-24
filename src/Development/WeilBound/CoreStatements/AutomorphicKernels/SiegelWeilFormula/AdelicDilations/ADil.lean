module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionDilationExp
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IsParOfFrame
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneSmulAdr

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem a_dil {d : SD σ} (R : RD d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) (h : d.G) : d.a (R.ι w y * h) = Real.exp (2 * τ) * d.a h ∧ 0 ≤ d.a h := by
  obtain ⟨hc, hfr⟩ : ∃ hc : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ, GlobalTheory.ThK.Dbl.inFrame d.b ((R.ι w) y) =
      Matrix.fromBlocks (↑(dilT hc w i₀ τ)) 0 0 ↑(dilT hc w i₀ (-τ)) :=
    ⟨_, inFrame_dil' R w i₀ τ y hy⟩
  obtain ⟨t, ht, hdet⟩ := PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame d (R.ι w y)
    (by rw [hfr, Matrix.toBlocks_fromBlocks₂₁])
  refine ⟨?_, ?_⟩
  · rw [PositivityTheory.SiegelWeilFormula.Avac.a_mul_par d ht h]
    congr 1
    have hdt : Matrix.GeneralLinearGroup.det t = Matrix.GeneralLinearGroup.det (dilT hc w i₀ τ) := by
      ext
      rw [hdet, hfr, Matrix.toBlocks_fromBlocks₁₁, Matrix.GeneralLinearGroup.val_det_apply]
    rw [hdt, det_dilT]
    exact absE_adrU hc w τ
  · obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa h
    rw [d.ok.hgt.val p t' hp k hk]
    exact NNReal.coe_nonneg _

end PositivityTheory.SiegelWeilFormula.AStep

end
