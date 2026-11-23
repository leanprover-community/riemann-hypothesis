module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr
open scoped TensorProduct

theorem UpperTheory.Gal.TP.Chr.readRes :
    UpperTheory.Gal.TP.Chr.ReadRes := by
  intro E _ _ _ μ χ hR hμ a
  rw [hR]
  have h3 : ∀ {σ : E →ₐ[↥(maximalRealSubfield E)] E} (h : HeckeCharacterZeroLocus.ThmBIn.IsCMExt (↥(maximalRealSubfield E)) E σ),
      Units.map ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv h).toRingHom
        : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E)
      (Units.map (algebraMap (AF ↥(maximalRealSubfield E)) (AE (↥(maximalRealSubfield E)) E)
        : AF ↥(maximalRealSubfield E) →* AE (↥(maximalRealSubfield E)) E) a)
      = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E a := fun _ =>
    Units.ext (GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap (a : AF ↥(maximalRealSubfield E)))
  erw [h3 (GlobalTheory.GalOfCusp.isCMExt_real E), hμ a]
  simp only [GlobalTheory.GalOfCusp.quadChar, MonoidHom.comp_apply]
  split_ifs with hm
  · obtain ⟨y, ⟨t, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 hm
    have hn : GlobalTheory.IdeleNormChar.normSign E a = 1 := by
      refine (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).2 ⟨t, ?_⟩
      rw [← hyz]
      simpa [GlobalTheory.QuadSymbol.toUnits, GlobalTheory.QuadSymbol.normGroup] using hz
    simp [hn]
  · rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with hn | hn
    · exfalso
      obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 hn
      exact hm (Subgroup.mem_sup.2 ⟨_, ⟨t, rfl⟩, _, ht, mul_div_cancel _ _⟩)
    · simp [hn]
