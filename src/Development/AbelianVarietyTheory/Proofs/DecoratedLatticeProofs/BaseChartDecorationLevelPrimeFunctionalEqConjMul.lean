module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasResOfValSubLt
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal

theorem base_deco_fn : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  intro B X I l Z u a Ch A hA i hi β P x hx r hr c hc
  choose y hy using (Formalism.L2.Col.mem_stdLat x).1 hx
  have hxy : x = fun j => (y j : B.fields.E) := funext fun j => (hy j).symm
  have hyc : y r = c := NumberField.RingOfIntegers.coe_injective ((hy r).trans hc.symm)
  rw [hxy, ← hyc]
  exact GlobalTheory.BaseFn.fn_eq (hA.base i hi β).1 (hA.base i hi β).2 P r hr _ (fun j => (hA.reads i hi).k_T β P r j hr) y

end GlobalTheory.PhiOneVal
