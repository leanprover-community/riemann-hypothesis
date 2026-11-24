module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.DetNeZeroOfNearOne
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.Imports
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.LFrob
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.RealPowerProductEqOne
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.ExtBasis
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.GermUnique
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.IsCompactSupport
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.IsCompactSupportSB
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.MeasurableSetBallM
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.MemBallMSelf
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.RepInvApply
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.ValLeOneOfLc
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds

@[expose] public section

open MeasureTheory GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel PositivityTheory.Tls2.Ming3 PositivityTheory.Rg.Ming
open scoped TensorProduct

namespace UpperTheory.Lit.HoweDuality

theorem lift_of_irr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ)
    (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W) (hrt : r < t)
    (hμs : IsSmoothChar μ) (hμu : IsUnitaryChar μ) (hσu : IsUnitarisable σ) (hπs : IsSmooth π) (hπi : π.IsIrreducible)
    (hIi : (prod₂ σ (detRep (Fin t) μ)).IsIrreducible) (hθ : ThetaPair μ σ π) :
    Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ))) := by
  have hstep := step ball (loc ball) nf rk (core ball rk)
  have hgerm := germ ball
  have huniq := uniq ball
  have hnz := nz ball (loc ball) nf
  have hlaw := law ball cov
  obtain ⟨B, hB0, hE⟩ := hθ
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.Model.exists_isUnitVol (k := k)
  have down : ∀ j, j ≤ r → VanRk B j → VanRk B 0 := fun j => by
    induction j with
    | zero => exact fun _ h => h
    | succ j ih => exact fun hj h => ih (by omega) (hstep k (r + t) r μ V W σ π B j (by omega) (by omega) hμu hσu hE h)
  obtain ⟨ev, hev⟩ := huniq k ν hν (r + t) r V W B _ (hgerm k ν hν r t μ V W σ π B hμs hπs hE)
  have hev0 : ev ≠ 0 := fun e => hB0 (LinearMap.ext fun Φ => down r le_rfl
    (hnz k ν hν r t μ V W σ π B hE fun w => (hev w 0).2 (by rw [e]; rfl)) Φ fun _ h => absurd h (Nat.not_lt_zero _))
  obtain ⟨f, hf⟩ := frob k r t μ V W σ π ev hπs hev0 (hlaw k ν hν r t μ V W σ π B hE ev hev)
  haveI := hπi
  haveI := hIi
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with h | h
  · exact ⟨.mk (LinearEquiv.ofBijective f.toLinearMap h) f.isIntertwining'⟩
  · exact absurd (by rw [h]; rfl) hf

end UpperTheory.Lit.HoweDuality
