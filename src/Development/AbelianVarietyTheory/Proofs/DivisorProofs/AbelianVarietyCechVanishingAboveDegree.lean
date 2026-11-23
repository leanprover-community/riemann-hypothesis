module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem not_NV_of_ge :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
      ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  intro K _ _ A _ hA
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hsep : IsSeparated A.hom := inferInstance
  obtain ⟨m, V, hV, hc⟩ :=
    GlobalTheory.exists_fin_affine_cover (X := A.left) (V := ⊤) (by simpa using isCompact_univ)
  refine ⟨m, fun P hP j hj hNV => ?_⟩
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hNV
  obtain ⟨e⟩ := GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers K A.left A.hom P κ W (Fin m) V
    hP hsep hW hWc hV hc j
  apply hne
  have hz : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).X j) :=
    GlobalTheory.AbLaw.isZero_cechLB_X A.hom P V (by simpa using hj)
  have h0 : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    ModuleCat.isZero_iff_subsingleton.1 h0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AmpleGen
