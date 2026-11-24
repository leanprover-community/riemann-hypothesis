module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceOfLocalAdmissible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove GlobalTheory.HeightCounting.SideCopy GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.SerGlue

theorem copyAll_ex {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}
    (h : CopyN D N ι e) (hp : HEq D.naut.plGw D'.naut.plGw) {D'' : D7} (hD : D'' = N.toD7) :
    ∃ ι' e', CopyAll D D'' ι' e' := by
  subst hD
  exact ⟨ι, e, h.cp, h.jL, h.s2, h.lamG, h.Xv, h.qs, hp⟩

theorem fr_same {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f.mu0 f'.mu0 ∧ HEq f.eta f'.eta ∧ HEq f.del f'.del ∧ HEq f.del' f'.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem choice_heq {A A' : Pre} (h : A' = A)
    {p : HeightOneSpectrum (𝓞 (maximalRealSubfield A.host.E)) → HeightOneSpectrum (𝓞 A.host.E)}
    {p' : HeightOneSpectrum (𝓞 (maximalRealSubfield A'.host.E)) → HeightOneSpectrum (𝓞 A'.host.E)}
    (hp : ∀ v, NG.OverPl (p v) v) (hp' : ∀ v, NG.OverPl (p' v) v)
    {s : HeightOneSpectrum (𝓞 A.host.F) → HeightOneSpectrum (𝓞 A.host.E)}
    {s' : HeightOneSpectrum (𝓞 A'.host.F) → HeightOneSpectrum (𝓞 A'.host.E)} (hs : HEq s' s)
    (r : Set.range p = Set.range s) (r' : Set.range p' = Set.range s') : HEq p p' := by
  subst h; cases hs
  refine heq_of_eq (funext fun v => ?_)
  obtain ⟨u, hu⟩ : p v ∈ Set.range p' := by rw [r', ← r]; exact ⟨v, rfl⟩
  have h1 := hp' u
  rw [hu] at h1
  obtain rfl : u = v := HeightOneSpectrum.ext (h1.symm.trans (hp v))
  exact hu.symm

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B}
  {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}

theorem bigHost_st (hO : K.Over B.toPre)
    (hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV)
    (x : St P) : BigHost (Dof x) :=
  ⟨(hB (w.st x.o.Z) hO).1, GlobalTheory.HeightCounting.FirstFacts.vstd_of_over (w.st x.o.Z) hO, (hB (w.st x.o.Z) hO).2⟩

end GlobalTheory.HeightCounting.SerGlue

end
