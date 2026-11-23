module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupBaseChangeIsConnIsEtPerfect
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

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem isTr_ofHom : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H) (l : Mod B H hH), IsTr B (RingHom.id k) hG hH (SemiHom.ofHom f) l (l ∘ₗ B.map (dual_conn hH) (dual_conn hG) (dualHom G H f)) := by
  intro p _ B k _ _ _ G H hG hH f l
  unfold IsTr
  letI : Algebra k k := (RingHom.id k).toAlgebra
  have hd := dual_conn hH
  have hd' := dual_conn hG
  have hb : (H.dual.baseChange k).IsConn := (baseChange_isConn_isEt p k k H.dual).1 hd
  let φ : H.dual ⟶ H.dual.baseChange k := SemiHom.lift (SemiHom.ofHom (𝟙 H.dual))
  have hφ : ∀ x, B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd (H.dual.toBase k) x) = x := by
    intro x
    rw [← B.smap_comp hd hb hd (H.dual.toBase k) (SemiHom.ofHom φ) (SemiHom.ofHom (𝟙 _)), B.smap_id]
    intro n a
    exact ((SemiHom.lift_app _ n 1 a).trans (one_smul _ _)).symm
  refine ⟨hb, l ∘ₗ B.map hd hb φ, fun x => ?_, fun y => ?_⟩
  · change l (B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd (H.dual.toBase k) x)) = _
    rw [hφ, WittVector.map_id, RingHom.id_apply]
  · have hc : ∀ n a, (SemiHom.ofHom ((PerfdLat.dualBaseChange k H).inv ≫
        dualHom G (H.baseChange k) (SemiHom.ofHom f).lift)).app n a =
        (H.dual.toBase k).app n ((SemiHom.ofHom (dualHom G H f)).app n a) := by
      intro n a
      change (CartierDual.baseChange k k (H.A n)).symm (CartierDual.map ((SemiHom.ofHom f).lift.app n) a) = (1 : k) ⊗ₜ CartierDual.map (f.app n) a
      apply EquivLike.injective (CartierDual.baseChange k k (H.A n))
      rw [BialgEquiv.apply_symm_apply]
      refine WithConv.ext (TensorProduct.AlgebraTensorModule.ext fun b m => ?_)
      simp
      rw [SemiHom.lift_app, SemiHom.ofHom_app, map_smul, smul_eq_mul, mul_comm]
    have key := B.smap_comp hb hd hd' (SemiHom.ofHom (dualHom G H f)) (H.dual.toBase k) _ hc y
    change l (B.map hd hd' (dualHom G H f) y) = l (B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd' _ y))
    rw [key, hφ]
    rfl

end GlobalTheory.Dieu.EtFromConn
