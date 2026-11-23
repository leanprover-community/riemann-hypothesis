module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock

@[expose] public section

open scoped TensorProduct ENNReal Matrix NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open PositivityTheory.Rg.Rsw

noncomputable section

namespace GlobalTheory.CompanionTheory.EisHolFam

open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

theorem eisHol_of_htExist : HtExist → EisHol := by
  intro _ D p χ _ c f hc hd hl h
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hsub : rightOf (max c ((p : ℝ) / 2)) ⊆ {z : ℂ | c < z.re} := fun z hz =>
    lt_of_le_of_lt (le_max_left _ _) (mem_rightOf.1 hz)
  have key := analyticOnNhd_cosetSum (P := P D p) (Γ := GF D p) (K := K D p) (δ := modP (D := D) (n := p))
    (χ := χ.comp detP) (ρ := (p : ℝ) / 2) (σ := max c ((p : ℝ) / 2)) (Φ := f) isIwasawa isCompact_K
    (hc.mono (Set.prod_mono hsub (Set.subset_univ _)))
    (fun z hz q g => by
      have := hl z (hsub hz) q q.2 (leviBlock (D := D) (n := p) q) rfl g
      push_cast
      exact this)
    (fun τ hτ => summable_spherical τ (lt_of_le_of_lt (le_max_right _ _) hτ))
    (fun g => (hd g).mono hsub) h
  refine key.differentiableOn.mono fun z hz => ?_
  exact mem_rightOf.2 (max_lt hz.1 hz.2)

end GlobalTheory.CompanionTheory.EisHolFam

end
