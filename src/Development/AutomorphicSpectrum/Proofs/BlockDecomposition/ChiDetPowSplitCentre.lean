module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open GlobalTheory.BCT.TwistDisc
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JoinDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Part (E : Type) [Field E] [NumberField E] [IsCMField E] where
  M : ℕ
  V : Submodule ℂ (Sm E M)
  σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin M) (w.adicCompletion E))
  m : (E →+* ℂ) → Multiset ℂ
  pos : 0 < M
  discrete : IsDiscrete V
  loc : ∀ w, IsLocCompGL V w (σ w)
  inf : ∀ τ, HasInfCharGL V τ (m τ)

def partOf {n : ℕ} (P : Pre E n) (i : Fin P.c) : Part E :=
  ⟨P.N i, P.V i, P.σ i, P.m i, P.pos i, P.discrete i, P.loc i, P.inf i⟩

def Part.twist (x : Part E) (χ : HChar E) (hu : χ.IsUnitary)
    (hs : ∀ (a : ℕ) (t : ℝ), chiDet a χ (splitCentre E a t) = 1) : Part E :=
  ⟨x.M, x.V.map (mulChi x.M χ).toLinearMap,
    fun w => (x.σ w).twist (CuspSub.locDet x.M χ w) (CuspSub.isOpen_ker_locDet χ w),
    fun τ => (x.m τ).map (· + expo χ τ), x.pos, isDiscrete_map hu (hs x.M) x.discrete,
    fun w => isLocCompGL_map χ (x.loc w), fun τ => hasInfCharGL_map (x.inf τ) χ⟩

def ofParts {n c : ℕ} (p : Fin c → Part E) (h : ∑ i, (p i).M = n) : Pre E n :=
  ⟨c, fun i => (p i).M, h, fun i => (p i).V, fun i => (p i).σ, fun i => (p i).m, fun i => (p i).pos,
    fun i => (p i).discrete, fun i => (p i).loc, fun i => (p i).inf⟩

theorem isUnitary_pow {μ : HChar E} {e : InfinitePlace E → ℤ} (hμ : IsMu μ e) (k : ℕ) : (μ ^ k).IsUnitary := fun x => by
  rw [pow_val_apply, Units.val_pow_eq_pow_val, norm_pow, hμ.1 x, one_pow]

theorem chiDet_pow_splitCentre {μ : HChar E} {e : InfinitePlace E → ℤ} (hμ : IsMu μ e) (k a : ℕ) (t : ℝ) :
    chiDet a (μ ^ k) (splitCentre E a t) = 1 := by
  show chiDet a μ _ ^ k = 1
  rw [chiDet_splitCentre hμ.2.2.2.2, one_pow]

theorem joinEx : JoinEx := by
  intro E _ _ _ n a b μ e Pa Pb hμ hn
  let p : Fin Pa.c → Part E := fun i =>
    (partOf Pa i).twist (μ ^ b) (isUnitary_pow hμ b) (chiDet_pow_splitCentre hμ b)
  let q : Fin Pb.c → Part E := fun i =>
    (partOf Pb i).twist (μ ^ a) (isUnitary_pow hμ a) (chiDet_pow_splitCentre hμ a)
  have hsum : ∑ i, (Fin.append p q i).M = n := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← hn]
    exact congrArg₂ (· + ·) Pa.h Pb.h
  refine ⟨ofParts (Fin.append p q) hsum, ?_⟩
  have h1 : parts (ofParts (Fin.append p q) hsum) =
      List.map (fun x : Part E => (⟨x.M, x.V⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) (List.ofFn (Fin.append p q)) := by
    rw [List.map_ofFn]
    rfl
  rw [IsJoin, h1, List.ofFn_fin_append, List.map_append, parts, parts, List.map_ofFn, List.map_ofFn, List.map_ofFn, List.map_ofFn]
  rfl

end GlobalTheory.CompanionTheory.JoinDatum

end
