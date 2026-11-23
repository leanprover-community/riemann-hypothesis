module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
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

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance

def reix (E : Type) [Field E] (n n' : ℕ) : Sp E n →ₗ[E] Sp E n' := LinearMap.pi fun l : Fin n' => atNL E n l.1

section Concrete

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev rkTop (R : Ranks) : ℕ := (R.N R.m - 1) + 0



open Classical in
def lamTop (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E)) (h : HomE X.E (rkTop R) (rkTop R)) : X.K :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.lamGBS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h
      else LocE.lamGB (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h)
  else LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P) R.r (R.N R.m - 1) h



abbrev Pt (u : Pr.Word) (i : ℕ) : Type := ChPt (R := R) sel mu u i × Option (L.β i) × Set (Sp X.E (R.N i))

variable (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)

end Concrete

section Global

variable {D : D7} {X : Fields} (s : Seam D X)

def ambE (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (e : TaylorLogMetric.FamE D) (dgen : D.what₂.Tau → ℂ) : Amb X where
  σ₀ := s.σ₀
  δ := δ
  d := D.host.d
  sc := (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
  AA := Submodule.span (𝓞 X.E)
    {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}
  cD τ := dgen (s.iT τ)
  e a b N N' z := e a b (s.lat N) (s.lat N') fun τ => z (s.iT.symm τ)
  chiF a b N N' := Base.chiFac χ a b (s.lat N) (s.lat N')


end Global

section Chain

variable {D : D7} {X : Fields} (s : Seam D X) {Pr : Primes X} (Ch : Chars X Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))
  (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop D.R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)
  {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (v : Pr.Word)
  (rep : ∀ i, C.cls i → Pt sel mu L v i)
  (frm : ∀ i, C.Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ)

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance
