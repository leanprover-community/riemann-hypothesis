module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def corrM (M : Model l K) (T : Corr l M.X) : Model l K := ⟨T.Z, T.p ≫ M.p⟩

def corrP (M : Model l K) (T : Corr l M.X) : E.gb (corrM M T) ⟶ E.gb M :=
  GlobalTheory.Et.geomMap (PadicAlgCl l) (corrM M T).q (Model.genMap (M := corrM M T) (N := M) T.p rfl) (Model.genMap_q (M := corrM M T) (N := M) T.p rfl)

def HkOfPush : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : Model l K) (T : Corr l M.X)
  (hr : T.r ≫ M.p = T.p ≫ M.p) (j : ℕ) (t : (corrM M T).V j →ₗ[ℚ_[l]] M.V j), LateralTheory.EtaleTrace.IsPush l (corrP M T) j t →
  IsHk M T hr j (t ∘ₗ Model.pullV (M := corrM M T) (N := M) T.r hr j)

end UpperTheory.Ru.crystallineComparison
