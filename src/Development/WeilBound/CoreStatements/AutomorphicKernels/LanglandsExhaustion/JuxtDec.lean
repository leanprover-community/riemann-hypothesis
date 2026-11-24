module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
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

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def FineUniqP : Prop :=
  ∀ (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Zc.Seg.dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ → τ.IsIrreducible →
    ∀ f : τ.IntertwiningMap (prodIrr (Zc.Seg.dec Δ) hd), Function.Injective f → IsLSeg Δ τ

theorem exists_emb_of_cast {h h' N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (e : h = h') (x : Fin h → IrrGL (k := k)) (y : Fin h' → IrrGL (k := k))
    (hxy : ∀ i, x i = y (Fin.cast e i)) (hd : ∑ a, (x a).1 = N) (f : τ.IntertwiningMap (prodIrr x hd))
    (hf : Function.Injective f) :
    ∃ hd' : ∑ a, (y a).1 = N, ∃ g : τ.IntertwiningMap (prodIrr y hd'), Function.Injective g := by
  subst e
  obtain rfl : x = y := funext fun i => by simpa using hxy i
  exact ⟨hd, f, hf⟩

theorem decW_get_eq (Γ : Segment k) (e : (decW Γ).length = Γ.len) (i : Fin (decW Γ).length) :
    (decW Γ).get i = Zc.Seg.dec Γ (Fin.cast e i) := by
  exact List.get_ofFn (fun a : Fin Γ.len => Γ.term (Fin.rev a)) i

theorem decLP (hF : FineUniqP k) : DecLP k := by
  intro Γ σ h
  obtain ⟨hd, f, hf⟩ := h
  have e : (decW Γ).length = Γ.len := List.length_ofFn
  obtain ⟨hd', g, hg⟩ := exists_emb_of_cast σ.rep e (decW Γ).get (Zc.Seg.dec Γ) (decW_get_eq Γ e) hd f hf
  exact hF Γ hd' σ.rep σ.2.rep.smooth σ.2.rep.irr g hg

end PositivityTheory.Exh

end
