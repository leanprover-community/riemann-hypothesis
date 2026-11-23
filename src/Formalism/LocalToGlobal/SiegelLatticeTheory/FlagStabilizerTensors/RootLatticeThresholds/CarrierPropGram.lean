module

public import Formalism.HermitianCurvature.StatementJCT
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
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

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Carrier

theorem propGram_of_vtTensor {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hB : Formalism.FourierDecayAlt.D.IsBuilt S T f χ ν' m₀ top A₀)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : Formalism.FourierDecayAlt.TB.Pt E → H)
    (hVt : Formalism.FourierDecayAlt.JCT.VtTensor S T f ν' m₀ Vt) : Formalism.FourierDecayAlt.C.PropGram S Vt := by
  exact Formalism.FourierDecayAlt.Final.jc_propGramOfPlaces E Wp Wq S
    _ (fun v => Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v) H Vt hVt
    (Formalism.FourierDecayAlt.Final.jc_gramPlaceBuilt Formalism.FourierDecayAlt.Final.d_ptPermSpec Formalism.FourierDecayAlt.Final.d_ptGSpec
      Formalism.FourierDecayAlt.Final.d_ptRelevant Formalism.FourierDecayAlt.Final.d_muRHaar Formalism.FourierDecayAlt.Final.jc_orbJCutScalar
      E Wp Wq S T f χ ν' m₀ top A₀ hg1 hg2 hB)

end Formalism.L2.SG.Pf.Carrier
