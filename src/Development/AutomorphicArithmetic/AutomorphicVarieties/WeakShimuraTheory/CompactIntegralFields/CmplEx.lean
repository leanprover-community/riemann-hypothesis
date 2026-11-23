module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CmplPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.cmplEx :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ (X : Space Φ a) (x : X.A →ₐ[Λ] ResidueField Λ), Φ.IsRes ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) →
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (f : X.A →ₐ[Λ] R),
        Φ.IsDef a (X.P.map (x : X.A →+* ResidueField Λ)) (X.P.map (f : X.A →+* R)) ∧ (f : X.A →+* R).Flat ∧ (res Λ R).comp f = x := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd X x hres
  haveI := X.noeth
  haveI := (co_res Λ).1
  obtain ⟨R, _, _, _, f, hflat, hfx, huniv⟩ := cmplPt x
  have hmap : ∀ {S T : Type} [CommRing S] [Algebra Λ S] [CommRing T] [Algebra Λ T]
      (u : X.A →ₐ[Λ] S) (h : S →ₐ[Λ] T),
      (X.P.map (u : X.A →+* S)).map (h : S →+* T) = X.P.map ((h.comp u : X.A →ₐ[Λ] T) : X.A →+* T) :=
    fun _ _ => rfl
  refine ⟨R, inferInstance, inferInstance, inferInstance, f, ⟨⟨X.pair_map f, X.cont_map f, ?_⟩, ?_⟩, hflat, hfx⟩
  · rw [hmap, hfx]
  · intro R' _ _ _ P' hP'
    obtain ⟨g, hg⟩ := X.univ R' _ P' hres hP'
    have hgx : (res Λ R').comp g = x := by
      exact X.hom_ext _ _ (by rw [← hmap, hg, hP'.red])
    obtain ⟨h, hh, hu⟩ := huniv R' g hgx
    refine ⟨h, ?_, fun h' hh' => hu h' ?_⟩
    · dsimp only
      rw [hmap, hh, hg]
    · dsimp only at hh' ⊢
      exact X.hom_ext _ _ (by rw [← hmap, hh', hg])
