module

public import Development.EtaleCohomology.EtaleSheaves.BoundaryKernel.Formal
public import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.EpiMono
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace LateralTheory.E.H0Kernel
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

theorem locSurj (B : Scheme.{0}) (q : ℕ) {F G : SShv B q} (e : F ⟶ G) [Epi e] : Sheaf.IsLocallySurjective e := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  exact (Sheaf.isLocallySurjective_iff_epi' _ e).2 inferInstance

theorem etale_sheaf_zeroth_cohomology_kernel_exact : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes := by
  intro B q M U x hx
  obtain ⟨T, e, he, H⟩ := exists_epi (C := SShv B q)
    (P := (presheafToSheaf (EtTop B) _).obj ((FP (ULift.{1} (ZMod q))).obj U)) x hx
  have := locSurj B q e
  obtain ⟨Z, hZ, hc⟩ := locally_factors (EtTop B) (ULift.{1} (ZMod q)) e
  refine ⟨Z, hZ, fun U' a ha => ?_⟩
  obtain ⟨c, hc⟩ := hc U' a ha
  have h := H _ c
  rw [← hc] at h
  exact h

end LateralTheory.E.H0Kernel
