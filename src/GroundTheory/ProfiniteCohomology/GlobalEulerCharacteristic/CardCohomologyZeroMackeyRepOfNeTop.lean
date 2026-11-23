module

public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf
public import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackey
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

instance isDiscreteRep_res_gsBaseChange_symm
    (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    [IsDiscreteRep B] : IsDiscreteRep (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) :=
  IsDiscreteRep.res (continuous_mulEquiv_toMonoidHom _) B

variable (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
  [IsDiscreteRep B]

theorem gsRealH0Card_coind (v : {v : InfinitePlace K.1 // v.IsReal}) :
    gsRealH0Card S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
        ιr v =
      ∏ d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom,
        Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom B d.out) 0) :=
  (Nat.card_congr (mackeyCohomologyEquiv (gsOpenSubgroup S hL) (gsRealFamily S ιr v) B 0).toEquiv).trans
    Nat.card_pi

theorem card_cohomology_zero_mackeyRep_of_ne_top (v : {v : InfinitePlace K.1 // v.IsReal})
    (d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom)
    (hd : ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom d.out = ⊤) :
    Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom B d.out) 0) = Nat.card B :=
  card_cohomology_zero_of_forall_eq_one _ fun g => by
    have hb := eq_bot_of_ne_top_realGal v _ hd
    have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 (hb ▸ g.2))
    subst hg
    exact map_one _

private theorem card_cohomology_zero_mackeyRep_top_aux
    {k G H J H' : Type} [CommRing k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H']
    (W : OpenSubgroup G) (φ : H →ₜ* G) (ψ : H' →ₜ* J)
    (β : (W : Subgroup G) ≃ₜ* J) (N : Rep k (W : Subgroup G)) [IsDiscreteRep N]
    [hN' : IsDiscreteRep (Rep.res β.symm.toMulEquiv.toMonoidHom N)]
    (x : G) (htop : mackeySubgroup (W : Subgroup G) φ.toMonoidHom x = ⊤)
    (e : H ≃* H')
    (he : ∀ (g : H) (hg : x * φ.toMonoidHom g * x⁻¹ ∈ (W : Subgroup G)),
      β ⟨x * φ.toMonoidHom g * x⁻¹, hg⟩ = ψ.toMonoidHom (e g)) :
    Nat.card (cohomology (mackeyRep (W : Subgroup G) φ.toMonoidHom N x) 0) =
      Nat.card (@cohomology k H' _ _ _ _ _
        (isDiscreteRep_res_toMonoidHom ψ (Rep.res β.symm.toMulEquiv.toMonoidHom N)) 0) := by
  let P := mackeySubgroup (W : Subgroup G) φ.toMonoidHom x
  let c := mackeyConj (W : Subgroup G) φ.toMonoidHom x
  have he' : Function.Surjective (fun g : P => e g.1) := fun g =>
    ⟨⟨e.symm g, (Subgroup.eq_top_iff' P).1 htop (e.symm g)⟩, e.apply_symm_apply g⟩
  have hconj (g : P) : β.symm (ψ.toMonoidHom (e g.1)) = c g :=
    (ContinuousMulEquiv.symm_apply_eq β).2 (he g.1 g.2).symm
  have hiff (b : N) : (∀ g : P, N.ρ (c g) b = b) ↔
      (∀ g : H', N.ρ (β.symm (ψ.toMonoidHom g)) b = b) := by
    constructor
    · intro hb g
      obtain ⟨a, rfl⟩ := he' g
      exact (congrArg (fun t => N.ρ t b) (hconj a)).trans (hb a)
    · intro hb a
      exact (congrArg (fun t => N.ρ t b) (hconj a).symm).trans (hb (e a.1))
  have hleft := Nat.card_congr
    (H0Iso (mackeyRep (W : Subgroup G) φ.toMonoidHom N x)).toLinearEquiv.toEquiv
  let _ := isDiscreteRep_res_toMonoidHom ψ (Rep.res β.symm.toMulEquiv.toMonoidHom N)
  have hright := Nat.card_congr
    (H0Iso (Rep.res ψ.toMonoidHom (Rep.res β.symm.toMulEquiv.toMonoidHom N))).toLinearEquiv.toEquiv
  exact hleft.trans ((Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans hright.symm)

theorem card_cohomology_zero_mackeyRep_top
    (ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
    (p : MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL)) (w : {w : InfinitePlace L.1 // w.IsReal})
    (e : Gal(AlgebraicClosure p.1.1.1.Completion / p.1.1.1.Completion) ≃*
      Gal(AlgebraicClosure w.1.Completion / w.1.Completion))
    (he : ∀ (g : Gal(AlgebraicClosure p.1.1.1.Completion / p.1.1.1.Completion))
      (hg : p.1.2.out * gsRealFamily S ιr p.1.1 g * p.1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
      gsBaseChange S hL ⟨p.1.2.out * gsRealFamily S ιr p.1.1 g * p.1.2.out⁻¹, hg⟩ =
        decompHomS w.1.Completion (placesOver S) (ιrL w) (e g)) :
    Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1.1).toMonoidHom B p.1.2.out) 0) =
      gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w := by
  unfold gsRealH0Card
  exact card_cohomology_zero_mackeyRep_top_aux (gsOpenSubgroup S hL) (gsRealFamily S ιr p.1.1)
    (gsRealFamily (placesOver S) ιrL w) (gsBaseChange S hL) B
    (hN' := isDiscreteRep_res_gsBaseChange_symm S hL B) p.1.2.out p.2 e he

end

end GroundTheory.ProfCoh
