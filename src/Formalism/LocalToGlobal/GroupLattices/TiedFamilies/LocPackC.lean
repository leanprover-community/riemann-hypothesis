module

public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.FillInstRecEqWj
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
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
import Mathlib.RingTheory.Ideal.Int
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

abbrev nFr (D : D7) (p : ℕ) : ℕ := orderOf (zH D.R.toFrame (hP D p))

theorem nFr_spec (D : D7) {T p : ℕ} (hg : GIdx D.host T p) : 2 ≤ nFr D p ∧ Even (nFr D p) := by
  obtain ⟨hp, -, -, hz, -, -⟩ := hg
  have hne : (Formalism.MainNotions.G.frobSet D p).Nonempty := by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨P, hPm, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E)
      (Ideal.span {(p : ℤ)})
    haveI : IsGalois ℚ D.host.E := D.host.galois
    obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (R := ℤ) (G := D.host.E ≃ₐ[ℚ] D.host.E) P
    exact ⟨_, P, hPm.isPrime, hPl, σ, hσ, rfl⟩
  obtain ⟨P, hP1, hP2, σ, hσ, hgal⟩ := Classical.epsilon_spec hne
  have hev : Even (orderOf (D.host.galE σ).2) := @hz P hP1 hP2 σ hσ
  rw [hgal] at hev
  have hA : addOrderOf (Formalism.MainNotions.G.hP D p) =
      orderOf (Classical.epsilon (fun g => g ∈ Formalism.MainNotions.G.frobSet D p)).2 := by
    unfold Formalism.MainNotions.G.hP
    exact Formalism.HC.Frame.addOrderOf_iotaInv _ _
  have hn : nFr D p = addOrderOf (Formalism.MainNotions.G.hP D p) := orderOf_zH _ _
  have hpos : 0 < orderOf (Classical.epsilon (fun g => g ∈ Formalism.MainNotions.G.frobSet D p)).2 := orderOf_pos _
  rw [hn, hA]
  refine ⟨?_, hev⟩
  obtain ⟨k, hk⟩ := hev
  rw [hk] at hpos ⊢
  omega

section Pack

variable (D : D7) (u : D.what₂.Word)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
  (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ nFr D (D.what₂.places.resChar w))
  (he : Even (nFr D (D.what₂.places.resChar w)))
  (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
    (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
    (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)

def locPackC : LocPack D u Lc (D.what₂.places.resChar w) where
  W := WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))
  Qq := QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))
  O := ORec D w (nFr D (D.what₂.places.resChar w))
  Kf := KfRec D w (nFr D (D.what₂.places.resChar w))
  ι := (extRec D w (nFr D (D.what₂.places.resChar w))).φK.comp
    (iota (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
  σ := sig (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))
  j := (extRec D w (nFr D (D.what₂.places.resChar w))).φ.comp
    (jO (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
  w := (extRec D w (nFr D (D.what₂.places.resChar w))).φ (wU (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
  hS := setting_ext (settingStd (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)) h5 h2 he)
    (extRec D w (nFr D (D.what₂.places.resChar w)))
  I := I
  ψ := ψ

end Pack

end Formalism.L2.G
