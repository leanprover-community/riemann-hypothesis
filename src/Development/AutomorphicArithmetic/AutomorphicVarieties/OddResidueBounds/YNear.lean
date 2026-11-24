module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.GroupRingIntAtDivSmulOfPadicValNatLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.TwistedBernoulliValueCongrPowMulFirst
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.yNear :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a r : ℕ) (ha : a.Coprime N), Odd a → l ^ (r + ck l (e + 1) + 1) ∣ N → IntAt l r (yEl (e + 1) a ha φ - coefMap ℚ Γ (ytEl e a φ)) := by
  intro l _ Γ _ _ N _ φ e a r ha hodd hdvd
  have hy := (Stk.twistedStickelbergerElements_agree N a ha Γ φ (e + 1)).1
  have hyt := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.1
  have hcf := (Stk.twistedStickelbergerElements_agree N a ha Γ φ e).2.2.2
  choose z hz using Stk.twistedBernoulliValue_congr_pow_mul_first N a e ha hodd
  rw [hy, hyt, hcf]
  have key : Stk.yForm (e + 1) a φ - Stk.cf ℚ Γ (Stk.ytEl e a φ)
      = ((N : ℚ) / (Stk.dk (e + 1) : ℚ)) • Stk.cf ℚ Γ (Stk.sumEl φ (fun b => -z b)) := by
    rw [Stk.cf_sumEl]
    unfold Stk.yForm Stk.ytEl
    rw [map_neg, Stk.cf_sumEl]
    unfold Stk.sumEl
    rw [neg_sub_neg, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hz _, MonoidAlgebra.smul_single]
    first
      | rw [← MonoidAlgebra.single_sub]
      | erw [← Finsupp.single_sub]
    congr 1
    simp only [smul_eq_mul]
    push_cast
    ring
  rw [key]
  have hN0 : N ≠ 0 := NeZero.ne N
  have hv := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hN0).mp hdvd
  apply Stk.groupRing_intAt_div_smul_of_padicValNat_le l N (Stk.dk (e + 1)) r (Nat.pos_of_ne_zero hN0) (Stk.dk_pos (Nat.succ_pos e))
  have hck : ck l (e + 1) = padicValNat l (Stk.dk (e + 1)) := rfl
  omega
