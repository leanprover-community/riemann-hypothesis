module

public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsDerivedOnOfIsKMod
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem fdAll_of (hM : ModelDS) (hF : FdModel) : FdAll := by
  intro n ε lam hl H _ _ σ hσ
  obtain ⟨T⟩ := HW.kType_exists ε lam hl
  obtain ⟨μ, hμ⟩ := S7.exists_mu hl
  have hDS := (hM n ε lam T μ hl hμ).2
  have hd := hF n ε lam T μ hl hμ
  obtain ⟨U, hU⟩ := GlobalTheory.CompanionTheory.DSUniq.ds_unique
    CompanionTheory.D.LK.hMultAlg CompanionTheory.D.LK.hKModExists CompanionTheory.D.LK.hOrthCyc
    n ε lam H _ σ (sigLam ε (PsiM T μ) T.w) hl hσ hDS
  have hc : ∀ (v w : H) (g : Formalism.REAL.UJ ε), Formalism.MainNotions.S.coefOn σ v w g =
      Formalism.MainNotions.S.coefOn (sigLam ε (PsiM T μ) T.w) (U v) (U w) g := by
    intro v w g
    simp only [Formalism.MainNotions.S.coefOn]
    rw [← hU _ g.2 v, LinearIsometryEquiv.inner_map_map]
  refine ⟨hd.1, fun v w v' w' => ?_⟩
  obtain ⟨h1, h2⟩ := hd.2 (U v) (U w) (U v') (U w')
  simp only [hc]
  refine ⟨h1, ?_⟩
  rw [h2, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

end PositivityTheory.RgFd
