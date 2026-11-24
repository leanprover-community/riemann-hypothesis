module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
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

@[expose] public section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N.TBLoc

section Len
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

end Len

end UpperTheory.N.TBLoc

namespace UpperTheory.N.TBLoc
section Clauses
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem tbe_clauses (L : Lattice (O := O) ρ) (I J : Subgroup G) (hIJ : I = J) (e cB : ℕ)
    (h2 : 0 < e → HfD PD L = BD L)
    (h3 : e = 0 → ∀ c : G → V ⧸ L.T, c ∈ HfD PD L ↔ (c ∈ divisibleCocycles L ∧ ∃ x, ∀ g ∈ J, c g = actD L g x - x))
    (hlen : Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) (((PD.p : ℕ) : O) ^ cB)) ≤
      (((Module.finrank Qp K + 1) * cB : ℕ) : ℕ∞) * lenOl PD (O := O)) :
    (0 < e → divisibleCocycles L ⊓ HfD PD L ≤ BD L) ∧
    (e = 0 → divisibleCocycles L ⊓ HfD PD L = divisibleCocycles L ⊓ (Z1urD L I ⊔ BD L)) ∧
    Module.length O (↥(divisibleCocycles L ⊓ (HfD PD L).comap ((((PD.p : ℕ) : O) ^ cB) • LinearMap.id)) ⧸
        (divisibleCocycles L ⊓ HfD PD L).comap (divisibleCocycles L ⊓ (HfD PD L).comap ((((PD.p : ℕ) : O) ^ cB) • LinearMap.id)).subtype) ≤
      ((Module.finrank Qp K : ℕ∞) + 1) * (cB : ℕ∞) * lenOl PD (O := O) := by
  exact GlobalTheory.TBLocal.tbe_clauses PD L I J hIJ e cB h2 h3 hlen
end Clauses
end UpperTheory.N.TBLoc

namespace UpperTheory.N.TBLoc
section Part1
open Formalism.MainNotions.LocalSituation

variable (S : Sit) [IsTopologicalRing S.LL] [IsDomain S.O] [IsPrincipalIdealRing S.O]
  (Yt : LocLat S.G S.Qp S.LL S.O) (p : Yt.V →ₗ[S.LL] S.LL) (e₀ : Yt.V) (hpe : p e₀ = 1)
  (hp : ∀ g v, p (Yt.ρ g v) = p v) (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap S.O S.LL))
  (he₀ : e₀ ∈ Yt.L.T) (hinj : Function.Injective (algebraMap S.O S.LL))

def incL : (kerY Yt p e₀ hpe hp hint he₀).V →ₗ[S.LL] Yt.V := (LinearMap.ker p).subtype

theorem incL_cont : Continuous (incL S Yt p e₀ hpe hp hint he₀) :=
  IsModuleTopology.continuous_of_linearMap _

def projL : Yt.V →ₗ[S.LL] (trivZ S.G S.Qp S.LL S.O hinj).V := p

theorem projL_cont : Continuous (projL S Yt p hinj) :=
  IsModuleTopology.continuous_of_linearMap _

def incHom : LatHom (kerY Yt p e₀ hpe hp hint he₀).L Yt.L :=
  { f := incL S Yt p e₀ hpe hp hint he₀
    equiv := fun _ _ => rfl
    cont := incL_cont S Yt p e₀ hpe hp hint he₀
    T_le := fun _ hx => hx }

def projHom : LatHom Yt.L (trivZ S.G S.Qp S.LL S.O hinj).L :=
  { f := projL S Yt p hinj
    equiv := fun g x => hp g x
    cont := projL_cont S Yt p hinj
    T_le := fun x hx => by
      obtain ⟨a, ha⟩ := hint x hx
      exact ⟨a, ha⟩ }

theorem ses : IsSESLat (Qp := S.Qp) (incHom S Yt p e₀ hpe hp hint he₀) (projHom S Yt p hp hint hinj) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext h
  · intro t
    let s : S.LL := t
    refine ⟨s • e₀, ?_⟩
    change p (s • e₀) = s
    rw [map_smul, hpe, smul_eq_mul, mul_one]
  · rintro y ⟨a, rfl⟩
    exact ⟨a • e₀, Yt.L.T.smul_mem a he₀, GlobalTheory.TBLocal.p_smul S Yt p e₀ hpe a⟩
  · intro x
    change p x = 0 ↔ ∃ y : LinearMap.ker p, (y : Yt.V) = x
    constructor
    · intro h
      exact ⟨⟨x, h⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  · intro y hy
    exact hy

include hinj in
theorem tb_part1 (E : S.Comparison₂) (hTB : TBat S E) (e M0 h0 cB : ℕ) (Ve : LocLat S.G S.Qp S.LL S.O)
    (h1 : Module.finrank S.LL Ve.V = 1)
    (hχ : ∀ g x, Ve.ρ g x = ((algebraMap S.Qp S.LL (S.PD.χ g : S.Qp))⁻¹) ^ e • x)
    (hCt : IsCrysOn S S.W.GKs Yt) (hWY : HypW S E (kerY Yt p e₀ hpe hp hint he₀) M0 h0)
    (hc : cTBY S (kerY Yt p e₀ hpe hp hint he₀) M0 h0 e ≤ cB)
    (φ : Yt.V →ₗ[S.O] (Ve.V ⧸ Ve.L.T))
    (hφ : ∀ g, ∀ y ∈ Yt.L.T, p y = 0 → φ (Yt.ρ g y) = actD Ve.L g (φ y)) :
    ((S.PD.p : S.O) ^ cB) • (fun g => φ (Yt.ρ g e₀ - e₀)) ∈ HfD S.PD Ve.L := by
  apply GlobalTheory.TBLocal.tb_part1 <;> assumption

end Part1
end UpperTheory.N.TBLoc

namespace UpperTheory.N.TBLoc
section Eps
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem eps_lat {V : Type} [AddCommGroup V] [Module LL V] [Module O V] {ρ : Representation LL G V}
    (T : Submodule O V) (e : ℕ) (h : IsMatLat (O := O) (ρ := ρ) T (epsTw PD e)) :
    Module.finrank LL V = 1 ∧ ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x := by
  exact GlobalTheory.TBLocal.eps_lat PD T e h
end Eps

end UpperTheory.N.TBLoc

end
