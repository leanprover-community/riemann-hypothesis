module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

namespace UpperTheory.GalN.V

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

structure AdmKN [IsCMField F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutCsdN ι r
  level : Level l M m r
  odd : Keep.OddU l r

end

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsScalarTower ℚ K Ω]


omit [IsAlgClosure ℚ Ω] [Algebra ℚ Ω] [IsScalarTower ℚ K Ω] in
structure Adm3N [IsCMField K] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop where
  irr : IsIrr ρ
  aut : IsAutCsdN ι (tw ρ (cycBar K Ω l)⁻¹)
  level : Level l N ![(e : ℤ), 0, -(e : ℤ)] ρ
  unl : Keep.OddU l ρ


omit [IsAlgClosure ℚ Ω] in
def Adm2N (ι : Qbar l ≃+* ℂ) (e M : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop :=
  ∃ W : G ℚ Ω →* GL (Fin 2) (Qbar l), IsIrr W ∧
    ((∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W) ∧
    Level l M ![(e : ℤ), -(e : ℤ)] W ∧ IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) ∧
    ∃ g : GL (Fin 3) (Qbar l), ∀ s : G K Ω, ((g * ρ s * g⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) =
      !![W (s.restrictScalars ℚ) 0 0, 0, W (s.restrictScalars ℚ) 0 1; 0, 1, 0;
         W (s.restrictScalars ℚ) 1 0, 0, W (s.restrictScalars ℚ) 1 1]

end

end UpperTheory.GalN.V
