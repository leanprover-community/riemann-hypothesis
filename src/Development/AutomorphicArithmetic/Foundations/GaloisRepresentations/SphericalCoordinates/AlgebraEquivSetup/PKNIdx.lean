module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem isOpen_map_conj {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    {K : Subgroup X} (hK : IsOpen (K : Set X)) (g : X) :
    IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  have e : ((K.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) =
      (fun x => g⁻¹ * x * g) ⁻¹' (K : Set X) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  rw [e]
  exact hK.preimage (by fun_prop)

theorem UpperTheory.Gal.W2.Seed.pKNIdx :
    KNOpen → KNIdx := by
  intro hop E _ _ _ A n p _ S T N hN
  obtain ⟨Lv, hLv⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p _ _ S.L N hN
  have hKo : IsOpen (S.L.KN N : Set S.G.GAf) := hLv ▸ Lv.K.isOpen
  have hKc : IsCompact (S.L.KN N : Set S.G.GAf) := hLv ▸ Lv.compact
  refine ⟨fun g => GlobalTheory.Mass.relIndex_ne_zero_of_isOpen hKc (isOpen_map_conj hKo g),
    fun K hKc' _ h0 => ?_⟩
  have hO := GlobalTheory.Mass.relIndex_ne_zero_of_isOpen hKc' (hop E A n p S T N hN)
  have e : S.L.KN N = ((S.L.KN N).comap T.j).comap T.sec := by
    ext h
    simp [Subgroup.mem_comap, T.j_sec]
  rw [e, Tr.lv, Subgroup.relIndex_comap] at h0
  exact hO (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)
