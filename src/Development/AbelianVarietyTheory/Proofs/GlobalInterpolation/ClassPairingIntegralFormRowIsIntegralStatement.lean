module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegral
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.classPairing_integral_form_row_isIntegral : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hI : I.Ok) (hQ : Q.Ok) (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (G : Q.Mt emb σ) (g : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ), (∀ w, (Q.per emb σ hI hQ hc).period w G = Q.ipP emb σ hQ g w) → ∀ (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] (y : Formalism.L2.DIV.VV K Q.sgT), y ∈ nabAt emb Q.sgT (Q.S'.Lsh c.1 (Q.S'.rep c)) → Q.rd emb σ G c = MvPolynomial.map σ y.1 → ∀ x ∈ (Q.S'.hlat emb Q.sgT hF).L, ∃ a : 𝓞 K, σ (a : K) = ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) * Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
  first | exact @GlobalTheory.PairAtClass.pair_integral | exact GlobalTheory.PairAtClass.pair_integral | (intros; apply GlobalTheory.PairAtClass.pair_integral <;> assumption)
