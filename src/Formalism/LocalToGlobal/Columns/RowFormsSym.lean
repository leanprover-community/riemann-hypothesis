module

public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Columns.LevGSym
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

open NumberField IsDedekindDomain

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section RBlockSym

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def rPsymF : LevFam X.E X.K R.r Pr.vGs := fun w =>
  ⟨HPsymF (𝓞 X.E ⧸ w.1.asIdeal) R.r R.k R.rS, chiSymF (Ch.psi0 w) R.r R.k R.rS⟩

theorem rowTyG_PsymF_H (w : {w // w ∈ Pr.vGs}) :
    (rowTyG Ch (rPsymF Ch) w).H = HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := rfl

end RBlockSym

end Formalism.L2.Col
