module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.SphComp

theorem form_heckeVec_dosetInd {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K)
    (l : Module.Dual ℂ V) (hl : ∀ k ∈ K, l ∘ₗ ρ k = l) (g : G) :
    l (heckeVec ρ K (dosetInd ℂ K g) x) =
      (Nat.card {c : G ⧸ K // (c.out : G) ∈ DoubleCoset.doubleCoset g (K : Set G) K} : ℂ) * l (ρ g x) := by
  classical
  set D := DoubleCoset.doubleCoset g (K : Set G) K with hD
  have hm := Formalism.UG.Final.DosetIndMem G K ℂ g
  have hfin : {c : G ⧸ K | c.out ∈ D}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets hK hm.2).subset ?_
    intro c hc
    have h' : c.out ∈ D := hc
    simp only [Set.mem_setOf_eq, dosetInd]
    rw [Set.indicator_of_mem h']
    simp
  have hterm : ∀ γ ∈ D, l (ρ γ x) = l (ρ g x) := by
    intro γ hγ
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hγ
    have e := LinearMap.congr_fun (hl a ha) (ρ g (ρ b x))
    simp only [LinearMap.comp_apply] at e
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, GlobalTheory.LGrp.mem_fixed.1 hx _ hb]
  have e1 : l (heckeVec ρ K (dosetInd ℂ K g) x) =
      ∑ᶠ c : G ⧸ K, l (dosetInd ℂ K g c.out • ρ c.out x) :=
    l.toAddMonoidHom.map_finsum (finite_heckeVec hK hm ρ x)
  have e2 : (fun c : G ⧸ K => l (dosetInd ℂ K g c.out • ρ c.out x)) =
      Set.indicator {c : G ⧸ K | c.out ∈ D} (fun _ => l (ρ g x)) := by
    funext c
    by_cases h : c.out ∈ D
    · have h1 : dosetInd ℂ K g c.out = 1 := by
        simp only [dosetInd]
        rw [Set.indicator_of_mem h]
        simp
      rw [Set.indicator_of_mem (show c ∈ {c : G ⧸ K | c.out ∈ D} from h), h1, one_smul, hterm _ h]
    · have h1 : dosetInd ℂ K g c.out = 0 := by
        simp only [dosetInd]
        exact Set.indicator_of_notMem h _
      rw [Set.indicator_of_notMem (show c ∉ {c : G ⧸ K | c.out ∈ D} from h), h1, zero_smul, map_zero]
  have hc : Nat.card {c : G ⧸ K // c.out ∈ D} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.card_coe_set_eq {c : G ⧸ K | c.out ∈ D}
  rw [e1, e2, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin, hc]
  simp

theorem sphCompare : PositivityTheory.SphericalProduct.SphCompare := by
  intro L _ _ ϖ σ q n hU V _ _ ρ α v₀ hv l hl g
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have e := congrArg l (hv.2.2 _ (Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g))
  rw [map_smul, smul_eq_mul, form_heckeVec_dosetInd hK ρ hv.2.1 l hl g] at e
  exact e

end GlobalTheory.CompanionTheory.SphComp

end
