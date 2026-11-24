module

public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem emb_mul_cc (g : R.GG) (x : H.E) : H.emb (g * R.cc) x = H.emb g (H.conj x) := by
  show H.φ₀ (H.sigmaOf (g * R.cc) x) = H.φ₀ (H.sigmaOf g (H.conj x))
  have : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj := map_mul (H.gal).symm g (R.cc)
  rw [this]; rfl

theorem conj_of_mem_F {x : H.E} (hx : x ∈ H.F) : H.conj x = x :=
  (H.conjE_mem_hostF_iff x).1 hx

theorem mul_cc_mem_Psi {g : R.GG} (hg : g ∉ R.Psi) : g * R.cc ∈ R.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
  show g.1.2 * (-1) = 1
  rcases Int.units_eq_one_or g.1.2 with h | h
  · exact absurd h hg
  · rw [h]; rfl

theorem realPl_surjective : Function.Surjective (realPl H) := by
  intro w
  have : Algebra.IsAlgebraic H.F H.E := Algebra.IsAlgebraic.tower_top (K := ℚ) H.F
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (K := H.E) w
  obtain ⟨g, hg⟩ := (factEmb R H).1.2 W.embedding
  have hW : InfinitePlace.mk (H.emb g) = W := by rw [hg]; exact InfinitePlace.mk_embedding W
  by_cases hgP : g ∈ R.Psi
  · refine ⟨⟨g, hgP⟩, ?_⟩
    rw [← hW]; exact (InfinitePlace.comap_mk _ _).symm
  · refine ⟨⟨g * R.cc, mul_cc_mem_Psi hgP⟩, ?_⟩
    have : (H.emb (g * R.cc)).comp H.F.subtype = (H.emb g).comp H.F.subtype := RingHom.ext fun x => by
      show H.emb (g * R.cc) (x : H.E) = H.emb g (x : H.E)
      rw [emb_mul_cc, conj_of_mem_F H x.2]
    rw [realPl, this, ← hW]; exact (InfinitePlace.comap_mk _ _).symm

theorem realPlBij : RealPlBij H := by
  refine (realPl_surjective H).bijective_of_nat_card_le ?_
  have h1 := IsTotallyReal.finrank (K := H.F)
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces H.F
  have h3 : Module.finrank ℚ H.F = R.f := H.finrank_hostF
  rw [(factCardPsi R H).1, Nat.card_eq_fintype_card, h2, ← h1, h3]
  omega

def tauPl (D : D7) : D.what₂.Tau ≃ InfinitePlace D.host.F :=
  D.eTau.trans (Equiv.ofBijective (realPl D.host) (realPlBij D.host))

end Formalism.L2.Host
