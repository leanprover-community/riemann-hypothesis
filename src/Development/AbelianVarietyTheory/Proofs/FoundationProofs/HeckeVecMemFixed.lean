module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.LFun.SatCompare

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {f f' : G → ℂ} {x : V}

theorem hAct_orbit (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) (x : V) (g : G) :
    hAct K f (fun y => ρ y x) g = ρ g (heckeVec ρ K f x) := by
  refine Eq.symm (((ρ g).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_))
  simp

theorem orbit_mem_amf (hx : x ∈ fixed ρ K) :
    (fun y => ρ y x) ∈ AMF ℂ ⊥ K (Representation.trivial ℂ (⊥ : Subgroup G) V) := by
  intro γ g κ
  have : (γ : G) = 1 := Subgroup.mem_bot.1 γ.2
  simp [this, GlobalTheory.LGrp.mem_fixed.1 hx κ κ.2]

theorem heckeVec_mem_fixed (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K f x ∈ fixed ρ K := by
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
  have := Final.HeckeActMem G ⊥ K ℂ V _ hK f hf _ (orbit_mem_amf hx) 1 1 ⟨k, hk⟩
  simpa [hAct_orbit hK hf] using this

theorem heckeVec_conv (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K (conv K f f') x = heckeVec ρ K f (heckeVec ρ K f' x) := by
  have := congrFun (Final.HeckeActMul G ⊥ K ℂ V _ hK f hf f' hf' _ (orbit_mem_amf hx)) 1
  rw [funext (hAct_orbit hK hf' ρ x), hAct_orbit hK hf,
    hAct_orbit hK (Final.HeckeConvMem G K ℂ hK f hf f' hf')] at this
  simpa using this

theorem heckeVec_one (hK : IsCommensurated K) (hx : x ∈ fixed ρ K) : heckeVec ρ K (dosetInd ℂ K 1) x = x := by
  have := congrFun (Final.HeckeActOne G ⊥ K ℂ V _ _ (orbit_mem_amf hx)) 1
  rw [hAct_orbit hK (Final.DosetIndMem G K ℂ 1)] at this
  simpa using this

theorem heckeVec_add_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (x : V) :
    heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  unfold heckeVec
  rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)]
  exact finsum_congr fun c => by simp [add_smul]

theorem heckeVec_smul_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K (c • f) x = c • heckeVec ρ K f x := by
  unfold heckeVec
  rw [smul_finsum' c (finite_heckeVec hK hf ρ x)]
  exact finsum_congr fun c => by simp [mul_smul]

theorem heckeVec_zero_left (x : V) : heckeVec ρ K 0 x = 0 := by simp [heckeVec]

def heckeLin (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) : V →ₗ[ℂ] V where
  toFun := heckeVec ρ K f
  map_add' x y := by
    unfold heckeVec
    rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf ρ y)]
    exact finsum_congr fun c => by simp
  map_smul' c x := (map_heckeVec hK hf (c • LinearMap.id) (fun g y => by simp) x).symm

@[simp] theorem heckeLin_apply (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (x : V) :
    heckeLin hK hf ρ x = heckeVec ρ K f x := rfl

theorem heckeVec_smul (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K f (c • x) = c • heckeVec ρ K f x := (heckeLin hK hf ρ).map_smul c x

end GlobalTheory.LFun.SatCompare

end
