module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitEv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.WtRat

theorem ev_spMap_top {R F : Type} [CommRing R] [CommRing F] (e : R →+* F)
    (h : ⊤ ≤ spMap e ⁻¹ᵁ ⊤) (u : Γ(Sp R, ⊤)) :
    ev (spMap e) ⊤ h u = e ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u) :=
  (ev_top (spMap e) h u).trans
    (congrArg (fun q => CommRingCat.Hom.hom q u)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom e)))

theorem exists_frac_ev (R : Type) [CommRing R] (W : (Sp R).Opens) (s : Γ(Sp R, W))
    (x : PrimeSpectrum R) (hx : x ∈ W) :
    ∃ α β : R, β ∉ x.asIdeal ∧ ∀ (F : Type) [Field F] (e : R →+* F) (h : ⊤ ≤ spMap e ⁻¹ᵁ W),
      WtRat.ev (spMap e) W h s * e β = e α := by
  have hT : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top (Sp R)
  obtain ⟨f, hfW, hxf⟩ := hT.exists_basicOpen_le (V := W) ⟨x, hx⟩ trivial
  have hb : (Sp R).basicOpen f =
      PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom f) :=
    basicOpen_eq_of_affine' f
  haveI := hT.isLocalization_basicOpen f
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers f)
    (((Sp R).presheaf.map (homOfLE hfW).op).hom s)
  set φ : Γ(Sp R, ⊤) →+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom with hφ
  refine ⟨φ a * φ f, φ f ^ (n + 1), ?_, ?_⟩
  · intro hm
    rw [hb] at hxf
    exact hxf (x.isPrime.mem_of_pow_mem _ hm)
  · intro F _ e h
    by_cases h0 : e (φ f) = 0
    · simp [h0]
    have hD : ⊤ ≤ spMap e ⁻¹ᵁ (Sp R).basicOpen f := by
      intro y _
      rw [hb]
      change e (φ f) ∉ y.asIdeal
      intro hy
      exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (Ne.isUnit h0))
    have key := congrArg (ev (spMap e) _ hD) ha
    rw [map_mul, ev_res (spMap e) hfW hD h s] at key
    have hv : ∀ u : Γ(Sp R, ⊤),
        ev (spMap e) _ hD (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen f) u) = e (φ u) :=
      fun u => (ev_res (spMap e) ((Sp R).basicOpen_le f) hD le_top u).trans
        (ev_spMap_top e le_top u)
    rw [hv, hv] at key
    simp only [map_pow] at key
    rw [map_pow, map_mul, pow_succ, ← _root_.mul_assoc, key]

end GlobalTheory.SS.WtRat
