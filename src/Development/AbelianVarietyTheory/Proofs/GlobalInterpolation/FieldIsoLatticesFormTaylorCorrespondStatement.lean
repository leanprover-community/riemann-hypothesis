module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.fieldIso_lattices_form_taylor_correspond : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b), z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N') ∧ (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Even a → Even b → IsSdLat N → IsSdLat N' → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) ∧ (∀ z w : TaylorLogMetric.VC D a b, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ))) ∧ ∀ G : TaylorLogMetric.VC D a b → ℂ, (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar X.Tau a b →₀ ℕ, derivAt0 (fun z : VCx X.Tau a b => G fun τ => z (s.iT.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  first | exact @GlobalTheory.SeamTransport.transport | exact GlobalTheory.SeamTransport.transport | (intros; apply GlobalTheory.SeamTransport.transport <;> assumption)
