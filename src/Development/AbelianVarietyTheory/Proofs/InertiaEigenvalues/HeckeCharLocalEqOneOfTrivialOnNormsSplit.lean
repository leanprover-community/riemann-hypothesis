module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.NormKill

theorem loc_eq_one_of_compNorm_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ε : Formalism.L2.Host.HChar (maximalRealSubfield E)),
    compNorm E ε = 1 → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∀ x, ε.loc v x = 1 := by
  intro E _ _ _ ε hε v hv x
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hnorm : Neutral.B1.localIdele (maximalRealSubfield E) v x ∈
      GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E
        (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) := by
    rw [GlobalTheory.IdeleNormChar.mem_normGroup_iff_everywhereNorm]
    refine ⟨fun w => ?_, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw
        have hx : GlobalTheory.IdeleNormChar.finComp (Neutral.B1.localIdele (maximalRealSubfield E) w x) w = x :=
          Units.ext (Neutral.B1.localIdele_snd_self _ w x)
        rw [hx]
        exact GlobalTheory.LFun.mem_normGroup_of_isSplit h2 hv x
      · have h1 : GlobalTheory.IdeleNormChar.finComp (Neutral.B1.localIdele (maximalRealSubfield E) v x) w = 1 := by
          apply Units.ext
          show (Neutral.B1.finiteSingle (maximalRealSubfield E) v (x : v.adicCompletion _)) w = 1
          exact GlobalTheory.LFun.finSingle_ne hw _
        rw [h1]
        exact one_mem _
    · have h1 : GlobalTheory.IdeleNormChar.infComp (Neutral.B1.localIdele (maximalRealSubfield E) v x) w = 1 :=
        Units.ext rfl
      rw [h1]
      exact one_mem _

  obtain ⟨z, hz⟩ := hnorm
  let y : (AdeleRing (𝓞 E) E)ˣ :=
    Units.map (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)).toRingHom.toMonoidHom z
  have hy : GlobalTheory.GalOfCusp.ideleNorm E y = Neutral.B1.localIdele (maximalRealSubfield E) v x := by
    apply Units.ext
    show Algebra.norm _ ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)).symm
      ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)) (z : _))) = _
    rw [RingEquiv.symm_apply_apply]
    exact congrArg Units.val hz
  have key : (GlobalTheory.GalOfCusp.compNorm E ε).1 y = (1 : Formalism.L2.Host.HChar E).1 y :=
    congrArg (fun χ : Formalism.L2.Host.HChar E => χ.1 y) hε
  rw [GlobalTheory.GalOfCusp.compNorm_apply, hy] at key
  exact key

end GlobalTheory.NormKill
