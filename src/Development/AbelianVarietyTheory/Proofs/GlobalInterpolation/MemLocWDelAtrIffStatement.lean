module

public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.mem_locW_delAtr_iff' : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (lam lam' : ι → DomWeight n), (∀ τ, (lam τ).natW = (lam' τ).natW) → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E M → ∀ (w : Pl.Pl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B → ∀ F : Formalism.L2.DIV.VV K lam, F ∈ locW Pl w (delAtr emb lam M) ↔ MvPolynomial.map σ (rhoVr emb lam B⁻¹ F).1 ∈ vlIntSpan σ Pl w lam' := by
  first | exact @GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff | exact GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff | (intros; apply GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff <;> assumption)
