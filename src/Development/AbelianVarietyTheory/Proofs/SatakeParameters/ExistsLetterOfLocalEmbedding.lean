module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem exists_aut_comp_eq_of_normal {E L : Type} [Field E] [CharZero E] [Normal ℚ E] [Field L]
    (f f' : E →+* L) : ∃ σ : E ≃ₐ[ℚ] E, ∀ x, f' x = f (σ x) := by
  haveI : CharZero L := (RingHom.charZero_iff f.injective).1 inferInstance
  letI : Algebra E L := f.toAlgebra
  haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun q => by
    change _ = f (algebraMap ℚ E q)
    simp
  obtain ⟨σ, hσ⟩ := (Normal.algHomEquivAut ℚ L E).symm.surjective f'.toRatAlgHom
  refine ⟨σ, fun x => ?_⟩
  have := DFunLike.congr_fun hσ x
  exact this.symm

theorem exists_letter_of_local_embedding : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), ∃ g : D.R.GG, (∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) = Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))) ∧ (Br.EmbTypeU D.nbr i w hw τ ↔ g ∈ D.R.Psi) := by
  intro D i w hw τ
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨σ, hσ⟩ := exists_aut_comp_eq_of_normal
    (((Br.toLLK (D.nbr i w hw)).comp (D.nd.embK i)).comp D.embE)
    ((τ : Br.Kw D.nbr i w hw →+* Br.LL D.nbr i w hw).comp (Br.cEw D.nbr i w hw))
  obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
  have hg' : D.host.sigmaOf g = σ := hg
  have key : ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) =
      Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x))) := by
    intro x
    rw [hg']
    exact hσ x
  have hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x := fun x =>
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)
  refine ⟨g, key, ?_, ?_⟩
  · rintro ⟨-, φ, hφ, h⟩
    have : D.host.emb g = φ := RingHom.ext fun x => by
      rw [← hemb x]
      exact h x _ (key x).symm
    exact ((factEmb D.R D.host).2 g).1 (this ▸ hφ)
  · intro hgP
    refine ⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g, ((factEmb D.R D.host).2 g).2 hgP, ?_⟩
    intro x y hy
    have hy' : y = D.embE (D.host.sigmaOf g x) :=
      (D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))
    rw [hy', hemb]

end GlobalTheory.HTW
