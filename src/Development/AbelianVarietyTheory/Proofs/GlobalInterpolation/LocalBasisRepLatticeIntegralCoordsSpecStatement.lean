module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalBasisRepLatticeIntegralCoordsSpec
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localBasisRepLattice_integralCoords_spec : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl), Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) (GlobalTheory.PerQ.Co.bP I u a w c) ∧ (∀ x, iniH (N_m_succ B.R) (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) = ((GlobalTheory.PerQ.Co.bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧ (∀ x, (I.perIn u a).tz * (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) = x (Br.iL (N_m_succ B.R))) ∧ Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) (GlobalTheory.PerQ.Co.bM I u a w c) := by
  first | exact @GlobalTheory.PerQ.Co.usage₉ | exact GlobalTheory.PerQ.Co.usage₉ | (intros; apply GlobalTheory.PerQ.Co.usage₉ <;> assumption)
