module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BalancedNonnegFormInPsdConeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaxSimplicialCellMultiplicityLtTopOfIsPolyFan
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite


open GlobalTheory.PolFan.MultBound in
theorem maxMult_lt_top : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O), IsPolyFan bar q φ → maxMult bar q φ < ⊤ := by
  intro O _ _ _ _ bar hCM q φ hφ
  obtain ⟨n, R, hR, hcls⟩ := hCM.classes q
  have hC := fun k : Fin n =>
    haveI := (hR k).1
    haveI := (hR k).2.1
    GlobalTheory.PolFan.MultBound.perModule (hφ (R k) (hR k).2.2) (GlobalTheory.T.balanced_nonneg_form_in_psd_cone O bar hCM (R k))
  choose C hC using hC
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    iSup_le fun hq => iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hli =>
      iSup_le fun hpr => ?_
  obtain ⟨k, ⟨e⟩⟩ := hcls X hq
  haveI := (hR k).1
  obtain ⟨h', hli', hpr', heq⟩ := GlobalTheory.PolFan.MultBound.transport e.symm h hli hpr
  have hle := (hC k m _ h' hli' hpr').trans (Finset.le_sup (f := C) (Finset.mem_univ k))
  rw [← heq]
  exact_mod_cast hle

end GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite
