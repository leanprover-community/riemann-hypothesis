module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Mathlib.Algebra.Order.PUnit
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothSmInd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinusStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport

section
section -- clump:auto
@[expose] public section

open GlobalTheory.PRep

namespace GlobalTheory.CompanionTheory.PRep

theorem twKer_eq_map_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (N : Subgroup G) (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W) (hf : Function.Surjective f)
    (hint : ∀ g v, f (ρ g v) = σ g (f v)) : twKer σ N θ = (twKer ρ N θ).map f := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨n, w', rfl⟩
    obtain ⟨v, rfl⟩ := hf w'
    exact ⟨ρ n v - (θ n : ℂ) • v, ⟨n, v, rfl⟩, by rw [map_sub, map_smul, hint]⟩
  · rintro ⟨_, ⟨n, v, rfl⟩, rfl⟩
    exact ⟨n, f v, by rw [map_sub, map_smul, hint]⟩

end GlobalTheory.CompanionTheory.PRep
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerEqMapOfSurjective =====

section -- clump:auto
@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.PRep.TwExact

theorem twMap_range_eq_ker : ∀ {G V₁ V₂ V₃ : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    (ρ₃ : Representation ℂ G V₃), IsSmooth ρ₁ → IsSmooth ρ₂ → IsSmooth ρ₃ →
    ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) →
    (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧
      IsCompact (L : Set G)) →
    ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v))
      (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v)), LinearMap.range f = LinearMap.ker g →
    LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg) := by
  intro G V₁ V₂ V₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ h₁ h₂ h₃ N θ hθ hN f g hf hg hfg
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer ρ₁ N θ) x
    rw [LinearMap.mem_ker]
    have hv : g (f v) = 0 := by
      have h0 : f v ∈ LinearMap.ker g := hfg ▸ LinearMap.mem_range_self f v
      exact LinearMap.mem_ker.mp h0
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, hv, Submodule.Quotient.mk_zero]
  · intro x hx
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer ρ₂ N θ) x
    rw [LinearMap.mem_ker] at hx
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    have hKinv : ∀ x : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (ρ₂ x) := by
      intro x u hu
      rw [Submodule.mem_comap, LinearMap.mem_ker, hg, LinearMap.mem_ker.mp hu, map_zero]
    let ρq : Representation ℂ G (V₂ ⧸ LinearMap.ker g) :=
      { toFun := fun x => (LinearMap.ker g).mapQ (LinearMap.ker g) (ρ₂ x) (hKinv x)
        map_one' := by
          ext u
          simp
        map_mul' := by
          intro x y
          ext u
          simp }
    have hq : GlobalTheory.PRep.IsSmooth ρq := by
      intro u
      obtain ⟨w0, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      rw [isOpen_iff_forall_mem_open]
      intro x0 hx0
      refine ⟨(fun y => x0 * y) '' {y | ρ₂ y w0 = w0}, ?_, isOpenMap_mul_left x0 _ (h₂ w0),
        ⟨1, by simp, by simp⟩⟩
      rintro _ ⟨y, hy, rfl⟩
      rw [Set.mem_ofPred_eq] at hy hx0 ⊢
      have e1 : ρq y (Submodule.Quotient.mk w0) = Submodule.Quotient.mk (ρ₂ y w0) := rfl
      rw [map_mul, Module.End.mul_apply, e1, hy, hx0]
    let gb : (V₂ ⧸ LinearMap.ker g) →ₗ[ℂ] V₃ := (LinearMap.ker g).liftQ g le_rfl
    have hgb_inj : Function.Injective gb := by
      intro a b hab
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      have hab' : g a = g b := hab
      rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, hab', sub_self]
    have hgb_eq : ∀ (x : G) (u : V₂ ⧸ LinearMap.ker g), gb (ρq x u) = ρ₃ x (gb u) := by
      intro x u
      obtain ⟨w0, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      exact hg x w0
    have hmem : (Submodule.Quotient.mk w : V₂ ⧸ LinearMap.ker g) ∈ GlobalTheory.PRep.twKer ρq N θ :=
      GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect ρq ρ₃ hq h₃ N θ hθ hN gb hgb_inj hgb_eq _ hx
    rw [_root_.GlobalTheory.CompanionTheory.PRep.twKer_eq_map_of_surjective ρ₂ ρq N θ (LinearMap.ker g).mkQ
      (Submodule.mkQ_surjective _) (fun x v => rfl)] at hmem
    obtain ⟨w', hw', hw'eq⟩ := hmem
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq, ← hfg, LinearMap.mem_range] at hw'eq
    obtain ⟨v, hv⟩ := hw'eq
    rw [LinearMap.mem_range]
    refine ⟨Submodule.Quotient.mk (-v), ?_⟩
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, map_neg, hv]
    rw [Submodule.Quotient.eq]
    have e2 : -(w' - w) - w = -w' := by abel
    rw [e2]
    exact Submodule.neg_mem _ hw'

end GlobalTheory.CompanionTheory.PRep.TwExact
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetExactSmooth =====
end


section
@[expose] public section

noncomputable section

open Matrix ValuativeRel GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZMirExhaust

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' {a b} ha hb := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    have hb' : valuation k b ≤ valuation k (s : k) := hb
    exact (Valuation.map_add _ a b).trans (max_le ha' hb')
  neg_mem' {a} ha := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    show valuation k (-a) ≤ valuation k (s : k)
    rwa [Valuation.map_neg]

theorem exists_ball_of_finset (T : Finset k) : ∃ s : kˣ, ∀ x ∈ T, x ∈ cball s := by
  classical
  refine Finset.induction_on T ?_ ?_
  · exact ⟨1, by simp⟩
  · intro a T _ ih
    obtain ⟨s, hs⟩ := ih
    by_cases h : valuation k a ≤ valuation k (s : k)
    · refine ⟨s, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h
      · exact hs x hx
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact h (by simp)
      refine ⟨Units.mk0 a ha0, fun x hx => ?_⟩
      show valuation k x ≤ valuation k a
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · have hx' : valuation k x ≤ valuation k (s : k) := hs x hx
        exact le_trans hx' (le_of_lt (not_le.1 h))

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

theorem continuous_colMat (n : ℕ) : Continuous (colMat k n) := by
  refine continuous_matrix fun i j => ?_
  unfold GlobalTheory.BZMir.colMat
  by_cases hj : j = Fin.last n
  · simp only [ite_eq_left hj]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · simp only [Fin.lastCases_castSucc]
      exact continuous_apply i
    · simp only [Fin.lastCases_last]
      exact continuous_const
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem continuous_unipMir (n : ℕ) :
    Continuous (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) := by
  have hval : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n v :=
    continuous_const.add (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hinv : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - GlobalTheory.BZMir.colMat k n v :=
    continuous_const.sub (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hGL : Continuous fun v : Fin n → k =>
      GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

def ballGroup (n : ℕ) (s : kˣ) : Subgroup (Mir k n) :=
  (AddSubgroup.toSubgroup (AddSubgroup.pi Set.univ fun _ : Fin n => ballSub s)).map (unipMir n)

theorem ballGroup_le (n : ℕ) (s : kˣ) : ballGroup (k := k) n s ≤ MirUin k n := by
  rintro _ ⟨v, -, rfl⟩
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

theorem coe_ballGroup (n : ℕ) (s : kˣ) : (ballGroup (k := k) n s : Set (Mir k n)) =
    (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) '' Set.univ.pi fun _ => cball s := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.coe_map]
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.toAdd v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.ofAdd v, hv, rfl⟩

theorem isCompact_ballGroup (n : ℕ) (s : kˣ) : IsCompact (ballGroup (k := k) n s : Set (Mir k n)) := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.coe_ballGroup]
  exact (isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s).image
    (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_unipMir n)

theorem exhaust (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.Exhaust k := by
  classical
  intro n S hS
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.BZMirExhaust.exists_ball_of_finset
    ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p =>
      ((p.1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc p.2) (Fin.last n))
  refine ⟨GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup n s, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup_le n s, ?_,
    GlobalTheory.CompanionTheory.BZMirExhaust.isCompact_ballGroup n s⟩
  intro g hg
  have hgU := hS hg
  rw [SetLike.mem_coe, GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hgU
  obtain ⟨v, hv⟩ := hgU
  rw [Finset.mem_coe] at hg
  rw [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.mem_map]
  refine ⟨v, ?_, Subtype.ext hv⟩
  show ∀ i ∈ Set.univ, Multiplicative.toAdd v i ∈ GlobalTheory.CompanionTheory.BZMirExhaust.ballSub s
  intro i _
  have hvi := GlobalTheory.BZMir.unip_apply_castSucc_last k n v i
  rw [hv] at hvi
  show Multiplicative.toAdd v i ∈ GlobalTheory.SplitWeil.cball s
  rw [← hvi]
  exact hs _ (Finset.mem_image.2 ⟨(g, i), Finset.mem_product.2 ⟨hg, Finset.mem_univ i⟩, rfl⟩)

end GlobalTheory.CompanionTheory.BZMirExhaust

end
end
end


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

theorem _root_.GlobalTheory.T.theta_open_mirabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ThetaOpen k := by
  first | exact @GlobalTheory.CompanionTheory.BZFun.thetaOpen
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEq\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustive\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetExactSmooth\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  intro ψ hψ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  have hopen : IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
    rw [_root_.GlobalTheory.CompanionTheory.BZMir.mirChar_eq_thetaA_single k ψ n]
    exact GlobalTheory.T.theta_open_mirabolic k ψ hψ (n + 1) _
  exact _root_.GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k (n + 1)) (mirChar k ψ n) hopen
    (_root_.GlobalTheory.CompanionTheory.BZMirExhaust.exhaust k (n + 1)) f g hf hg hfg

end GlobalTheory.CompanionTheory.BZMir
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustive\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetExactSmooth\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPsiMinus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZMir.Fun.ExPsiMinus k := by
  intro k _ _ _ _ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  refine _root_.GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k n) 1 ?_ (_root_.GlobalTheory.CompanionTheory.BZMirExhaust.exhaust k n) f g hf hg hfg
  have hker : ((1 : MirUin k n →* ℂˣ).ker : Set (MirUin k n)) = Set.univ := by
    ext x
    simp
  rw [hker]
  exact isOpen_univ

end GlobalTheory.CompanionTheory.BZMir
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn\npublic import Mathlib.Algebra.Order.PUnit\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothSmInd\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinusStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

def Ses {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    (ρ₃ : Representation ℂ G V₃) : Prop :=
  ∃ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃), (∀ x v, f (ρ₁ x v) = ρ₂ x (f v)) ∧ (∀ x v, g (ρ₂ x v) = ρ₃ x (g v)) ∧
    Function.Injective f ∧ Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable def iterN (ψ : AddChar k Circle) {n : ℕ} : (j : ℕ) → MRep k (n + j) → MRep k n
  | 0, τ => τ
  | j + 1, τ => iterN ψ j (phiN ψ τ)

def dN (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) (τ : MRep k (n + j)) : GRep k n := psiN (iterN ψ j τ)

noncomputable def dG (ψ : AddChar k Circle) : (j : ℕ) → {n : ℕ} → GRep k (n + j) → GRep k n
  | 0, _, σ => σ
  | j + 1, _, σ => dN ψ j (gres σ)

inductive Chain {n : ℕ} (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) : ℕ → ℕ → GRep k n → Prop
  | nil (a : ℕ) (X : GRep k n) : Subsingleton X.V → Chain R Z a a X
  | step {a b : ℕ} {X Y A : GRep k n} : R a A → Ses Y.ρ X.ρ A.ρ → Chain R Z (a + 1) b Y → Chain R Z a b X
  | skip {a b : ℕ} {X Y : GRep k n} : Z a → GIso Y X → Chain R Z (a + 1) b Y → Chain R Z a b X

def RF (ψ : AddChar k Circle) {r t n : ℕ} (π₁ : GRep k r) (π₂ : GRep k t) (ℓ a : ℕ) (A : GRep k n) : Prop :=
  ∃ (c r' t' : ℕ) (_ : a + c = ℓ) (h₁ : r = r' + a) (h₂ : t = t' + c) (hs : r' + t' = n),
    GIso A (((dG ψ a (π₁.cast h₁)).prod (dG ψ c (π₂.cast h₂))).cast hs)

def RP (ψ : AddChar k Circle) {i t n : ℕ} (τ : MRep k i) (σ : GRep k t) (j a : ℕ) (A : GRep k n) : Prop :=
  ∃ (b c i' t' : ℕ) (_ : a = b + 1) (_ : b + c = j) (hi : i = i' + b) (ht : t = t' + c) (hs : i' + t' = n),
    GIso A (((dN ψ b (mcast hi τ)).prod (dG ψ c (σ.cast ht))).cast hs)

def ZP (i t j a : ℕ) : Prop := ¬ (a ≤ i + 1 ∧ j + 1 - a ≤ t)

def ZF (r t ℓ a : ℕ) : Prop := ¬ (a ≤ r ∧ ℓ - a ≤ t)

section basic
variable {G M V₁ V₂ V₃ : Type} [Group G] [Group M] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃]

theorem ses_twist {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} {ρ₃ : Representation ℂ G V₃} (χ : G →* ℂˣ)
    (h : Ses ρ₁ ρ₂ ρ₃) : Ses (twist ρ₁ χ) (twist ρ₂ χ) (twist ρ₃ χ) := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ⟨f, g, fun x v => ?_, fun x v => ?_, hi, hs, he⟩
  · simp [GlobalTheory.SmGL.twist_apply, hf]
  · simp [GlobalTheory.SmGL.twist_apply, hg]

theorem ses_twAct {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} {ρ₃ : Representation ℂ G V₃}
    (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v)) (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v))
    (hsurj : Function.Surjective g)
    (h0 : LinearMap.ker (twMap ρ₁ ρ₂ N θ f hf) = ⊥)
    (h1 : LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg)) :
    Ses (twAct ρ₁ N θ s hs) (twAct ρ₂ N θ s hs) (twAct ρ₃ N θ s hs) := by
  refine ⟨twMap ρ₁ ρ₂ N θ f hf, twMap ρ₂ ρ₃ N θ g hg, fun x v => ?_, fun x v => ?_, LinearMap.ker_eq_bot.1 h0, ?_, h1⟩
  · induction v using Submodule.Quotient.induction_on with
    | H v => exact congrArg Submodule.Quotient.mk (hf (s x) v)
  · induction v using Submodule.Quotient.induction_on with
    | H v => exact congrArg Submodule.Quotient.mk (hg (s x) v)
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨v, rfl⟩ := hsurj y
      exact ⟨Submodule.Quotient.mk v, rfl⟩

end basic

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmooth_punit {G : Type} [Group G] [TopologicalSpace G] : IsSmooth (Representation.trivial ℂ G PUnit) := by
  intro v
  have : {g : G | Representation.trivial ℂ G PUnit g v = v} = Set.univ := by ext g; simp
  rw [this]; exact isOpen_univ

theorem ses_phiN (ψ : AddChar k Circle) (hc : Continuous ψ) {n : ℕ} {A B C : MRep k (n + 1)} (hA : IsSmooth A.ρ) (hB : IsSmooth B.ρ)
    (hC : IsSmooth C.ρ) (h : Ses A.ρ B.ρ C.ρ) : Ses (phiN ψ A).ρ (phiN ψ B).ρ (phiN ψ C).ρ := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ses_twist _ (ses_twAct (MirUin k (n + 1)) (mirChar k ψ n) _ (levi_stab ψ n) f g hf hg hs ?_ (_root_.GlobalTheory.CompanionTheory.BZMir.exPhiMinus k ψ hc n _ _ _ _ _ _ hA hB hC f g hf hg he))
  have h0 := _root_.GlobalTheory.CompanionTheory.BZMir.exPhiMinus k ψ hc n PUnit _ _ (Representation.trivial ℂ _ PUnit) A.ρ B.ρ isSmooth_punit hA hB 0 f
    (fun _ _ => by simp) hf (by rw [LinearMap.range_zero, LinearMap.ker_eq_bot.2 hi])
  rw [← h0, LinearMap.range_eq_bot]
  ext x
  simp [twMap]

theorem ses_psiN {n : ℕ} {A B C : MRep k n} (hA : IsSmooth A.ρ) (hB : IsSmooth B.ρ)
    (hC : IsSmooth C.ρ) (h : Ses A.ρ B.ρ C.ρ) : Ses (psiN A).ρ (psiN B).ρ (psiN C).ρ := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ses_twist _ (ses_twAct (MirUin k n) 1 (levi k n) (levi_normalises n) f g hf hg hs ?_ (_root_.GlobalTheory.CompanionTheory.BZMir.exPsiMinus k n _ _ _ _ _ _ hA hB hC f g hf hg he))
  have h0 := _root_.GlobalTheory.CompanionTheory.BZMir.exPsiMinus k n PUnit _ _ (Representation.trivial ℂ _ PUnit) A.ρ B.ρ isSmooth_punit hA hB 0 f
    (fun _ _ => by simp) hf (by rw [LinearMap.range_zero, LinearMap.ker_eq_bot.2 hi])
  rw [← h0, LinearMap.range_eq_bot]
  ext x
  simp [twMap]

theorem isSmooth_phiN (ψ : AddChar k Circle) {n : ℕ} {A : MRep k (n + 1)} (hA : IsSmooth A.ρ) : IsSmooth (phiN ψ A).ρ :=
  isSmooth_twist (_root_.GlobalTheory.CompanionTheory.BZMirSmooth.smPhiMinus k ψ n _ A.ρ hA)
    (IsSmoothChar.comp (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _)) _ continuous_subtype_val)

theorem isSmooth_psiN {n : ℕ} {A : MRep k n} (hA : IsSmooth A.ρ) : IsSmooth (psiN A).ρ :=
  isSmooth_twist (_root_.GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus k n _ A.ρ hA) (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))

theorem isSmooth_prodGPn {m j : ℕ} (ρ : GRep k m) (τ : MRep k j) : IsSmooth (prodGPn ρ τ).ρ :=
  GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd _ _

theorem isSmooth_prodPGn {i t : ℕ} (τ : MRep k i) (σ : GRep k t) : IsSmooth (prodPGn τ σ).ρ :=
  GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd _ _

theorem isSmooth_mcast {a b : ℕ} (h : a = b) {τ : MRep k a} (hτ : IsSmooth τ.ρ) : IsSmooth (mcast h τ).ρ := by
  subst h; exact hτ

theorem isSmooth_gres {n : ℕ} {π : GRep k (n + 1)} (h : IsSmooth π.ρ) : IsSmooth (gres π).ρ :=
  isSmooth_comp h _ continuous_subtype_val

end

section iso
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ}

theorem eint {V W : Type} {G : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (x : G) (v : V) : e (ρ x v) = σ x (e v) :=
  e.toIntertwiningMap.isIntertwining _ _ x v
theorem giso_refl (A : GRep k n) : GIso A A := ⟨Representation.Equiv.refl _⟩
theorem giso_symm {A B : GRep k n} (h : GIso A B) : GIso B A := h.map (·.symm)
theorem giso_trans {A B C : GRep k n} (h : GIso A B) (h' : GIso B C) : GIso A C := by
  obtain ⟨e⟩ := h; obtain ⟨e'⟩ := h'; exact ⟨e.trans e'⟩
theorem miso_refl (A : MRep k n) : MIso A A := ⟨Representation.Equiv.refl _⟩
theorem miso_symm {A B : MRep k n} (h : MIso A B) : MIso B A := h.map (·.symm)
theorem miso_trans {A B C : MRep k n} (h : MIso A B) (h' : MIso B C) : MIso A C := by
  obtain ⟨e⟩ := h; obtain ⟨e'⟩ := h'; exact ⟨e.trans e'⟩
theorem giso_tw {A B : GRep k n} (s : ℝ) (h : GIso A B) : GIso (A.tw s) (B.tw s) := by
  obtain ⟨e⟩ := h
  exact ⟨Representation.Equiv.mk e.toLinearEquiv fun x => by
    ext v
    show e (((dpow n s x : ℂˣ) : ℂ) • A.ρ x v) = ((dpow n s x : ℂˣ) : ℂ) • B.ρ x (e v)
    rw [map_smul]
    exact congrArg _ (eint e x v)⟩
theorem miso_mcast {a b : ℕ} (h : a = b) {A B : MRep k a} (e : MIso A B) : MIso (mcast h A) (mcast h B) := by
  subst h; exact e
theorem giso_cast {a b : ℕ} (h : a = b) {A B : GRep k a} (e : GIso A B) : GIso (A.cast h) (B.cast h) := by
  subst h; exact e
theorem tw_cast {a b : ℕ} (h : a = b) (A : GRep k a) (s : ℝ) : GIso ((A.cast h).tw s) ((A.tw s).cast h) := by
  subst h; exact giso_refl _
theorem giso_prod {r t : ℕ} {A A' : GRep k r} {B B' : GRep k t} (e : GIso A A') (e' : GIso B B') :
    GIso (A.prod B) (A'.prod B') := by
  obtain ⟨e⟩ := e
  obtain ⟨e'⟩ := e'
  exact ⟨GlobalTheory.LocGL.multiProdEquiv _ (fun x => match x with
    | false => e
    | true => e')⟩
end iso

section ses
variable {G V₀ V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
  {ρ₀ : Representation ℂ G V₀} {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂} {ρ₃ : Representation ℂ G V₃}

theorem ses_mid (e : ρ₂.Equiv ρ₀) (h : Ses ρ₁ ρ₂ ρ₃) : Ses ρ₁ ρ₀ ρ₃ := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ⟨e.toLinearEquiv.toLinearMap ∘ₗ f, g ∘ₗ e.symm.toLinearEquiv.toLinearMap, fun x v => ?_, fun x v => ?_,
    e.toLinearEquiv.injective.comp hi, hs.comp e.symm.toLinearEquiv.surjective, ?_⟩
  · show e (f (ρ₁ x v)) = ρ₀ x (e (f v))
    rw [hf]; exact eint e x _
  · show g (e.symm (ρ₀ x v)) = ρ₃ x (g (e.symm v))
    rw [← hg]
    exact congrArg g (eint e.symm x v)
  · ext y
    constructor
    · rintro ⟨v, rfl⟩
      have : f v ∈ LinearMap.ker g := he ▸ LinearMap.mem_range_self f v
      simpa [LinearMap.mem_ker, Representation.Equiv.symm_apply_apply] using this
    · intro hy
      have : e.symm y ∈ LinearMap.range f := he ▸ hy
      obtain ⟨v, hv⟩ := this
      exact ⟨v, by simp [hv]⟩

theorem ses_right (e : ρ₃.Equiv ρ₀) (h : Ses ρ₁ ρ₂ ρ₃) : Ses ρ₁ ρ₂ ρ₀ := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  refine ⟨f, e.toLinearEquiv.toLinearMap ∘ₗ g, hf, fun x v => ?_, hi, e.toLinearEquiv.surjective.comp hs, ?_⟩
  · show e (g (ρ₂ x v)) = ρ₀ x (e (g v))
    rw [hg]
    exact eint e x _
  · rw [he]
    ext y
    simp

theorem ses_zero_left (e : ρ₂.Equiv ρ₃) [Subsingleton V₁] : Ses ρ₁ ρ₂ ρ₃ := by
  refine ⟨0, e.toLinearEquiv.toLinearMap, fun x v => by simp, fun x v => eint e x v,
    Function.injective_of_subsingleton _, e.toLinearEquiv.surjective, ?_⟩
  rw [LinearMap.range_zero]
  exact (LinearEquiv.ker e.toLinearEquiv).symm

theorem equiv_of_ses_zero (h : Ses ρ₁ ρ₂ ρ₃) [Subsingleton V₃] : Nonempty (ρ₁.Equiv ρ₂) := by
  obtain ⟨f, g, hf, hg, hi, hs, he⟩ := h
  have hsurj : Function.Surjective f := by
    intro y
    have : y ∈ LinearMap.range f := by rw [he]; exact Subsingleton.elim (g y) 0
    exact this
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective f ⟨hi, hsurj⟩) fun x => by
    ext v; exact hf x v⟩

end ses

section chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {R R' : ℕ → GRep k n → Prop} {Z Z' : ℕ → Prop}

def zeroG (n : ℕ) : GRep k n := ⟨PUnit, Representation.trivial ℂ _ PUnit⟩

instance (n : ℕ) : Subsingleton (zeroG (k := k) n).V := inferInstanceAs (Subsingleton PUnit)

theorem subsingleton_of_giso {A B : GRep k n} (h : GIso A B) [Subsingleton A.V] : Subsingleton B.V := by
  obtain ⟨e⟩ := h
  exact e.symm.toLinearEquiv.injective.subsingleton

theorem Chain.iso {a b : ℕ} {X X' : GRep k n} (h : Chain R Z a b X) (e : GIso X X') : Chain R Z a b X' := by
  cases h with
  | nil a X hs => exact Chain.nil _ _ (subsingleton_of_giso e)
  | step hR hs hc => obtain ⟨e⟩ := e; exact Chain.step hR (ses_mid e hs) hc
  | skip hZ he hc => exact Chain.skip hZ (giso_trans he e) hc

theorem Chain.mono {a b : ℕ} {X : GRep k n} (h : Chain R Z a b X) (hR : ∀ c A, R c A → R' c A) (hZ : ∀ c, Z c → Z' c) :
    Chain R' Z' a b X := by
  induction h with
  | nil a X hs => exact Chain.nil _ _ hs
  | step h hs _ ih => exact Chain.step (hR _ _ h) hs ih
  | skip h he _ ih => exact Chain.skip (hZ _ h) he ih

theorem Chain.shift {a b : ℕ} {X : GRep k n} (h : Chain R Z a b X) (hR : ∀ c A, R c A → R' (c + 1) A)
    (hZ : ∀ c, Z c → Z' (c + 1)) : Chain R' Z' (a + 1) (b + 1) X := by
  induction h with
  | nil a X hs => exact Chain.nil _ _ hs
  | step h hs _ ih => exact Chain.step (hR _ _ h) hs ih
  | skip h he _ ih => exact Chain.skip (hZ _ h) he ih

theorem chain_zero {X : GRep k n} (hX : Subsingleton X.V) : ∀ (d a : ℕ), (∀ c, a ≤ c → c < a + d → Z c) →
    Chain R Z a (a + d) X := by
  intro d
  induction d with
  | zero => intro a _; exact Chain.nil _ _ hX
  | succ d ih =>
    intro a h
    refine Chain.skip (h a le_rfl (by omega)) (giso_refl X) ?_
    have := ih (a + 1) (fun c h1 h2 => h c (by omega) (by omega))
    rwa [show a + 1 + d = a + (d + 1) by omega] at this

def Top (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) (a : ℕ) (C : GRep k n) : Prop :=
  (∃ A, R a A ∧ GIso C A) ∨ (Z a ∧ Subsingleton C.V)

theorem chain_top {a b : ℕ} {X Y C : GRep k n} (hs : Ses Y.ρ X.ρ C.ρ) (ht : Top R Z a C)
    (hc : Chain R Z (a + 1) b Y) : Chain R Z a b X := by
  rcases ht with ⟨A, hR, ⟨e⟩⟩ | ⟨hZ, h0⟩
  · exact Chain.step hR (ses_right e hs) hc
  · exact Chain.skip hZ (equiv_of_ses_zero hs) hc

theorem chain_top' {a : ℕ} {X : GRep k n} (ht : Top R Z a X) (d : ℕ) (hZ : ∀ c, a + 1 ≤ c → c < a + 1 + d → Z c) :
    Chain R Z a (a + 1 + d) X := by
  obtain ⟨e⟩ : Nonempty (X.ρ.Equiv X.ρ) := ⟨Representation.Equiv.refl _⟩
  exact chain_top (Y := zeroG n) (ses_zero_left e) ht (chain_zero inferInstance d _ hZ)

theorem Chain.tw {a b : ℕ} {X : GRep k n} (s : ℝ) (h : Chain R Z a b X) :
    Chain (fun c A' => ∃ A, R c A ∧ GIso A' (A.tw s)) Z a b (X.tw s) := by
  induction h with
  | nil a X hs => exact Chain.nil _ _ hs
  | step h hs _ ih => exact Chain.step ⟨_, h, giso_refl _⟩ (ses_twist _ hs) ih
  | skip h he _ ih => exact Chain.skip h (giso_tw s he) ih

end chain

end GlobalTheory.CompanionTheory.LeibOrd

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso =====
