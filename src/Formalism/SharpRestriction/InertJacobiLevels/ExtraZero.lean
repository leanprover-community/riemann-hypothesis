import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain



theorem locLe_of_subsingleton {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    [Subsingleton V] (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (A B : Submodule (𝓞 K) V) : DV.LocLe w k A B :=
  fun x _ => ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [Subsingleton.elim ((1 : 𝓞 K) • x) 0]; exact Submodule.zero_mem _⟩




def lieOfSubsingleton (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [Subsingleton V] [Subsingleton W] : V ≃ₗᵢ[ℂ] W :=
  ⟨LinearEquiv.ofSubsingleton V W, fun x => by
    rw [Subsingleton.elim x 0, map_zero, norm_zero, norm_zero]⟩

set_option synthInstance.maxHeartbeats 200000 in

def rowSideZero (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    [Subsingleton EE] : RowSide D EE where
  Amb := fun _ => Z0
  Mult := fun _ _ => Z0
  multZero := fun _ => lieOfSubsingleton _ _
  multTop := fun _ => LinearIsometryEquiv.refl ℂ Z0
  io := fun _ _ => 0
  Mtilde := fun _ => zeroOLat _
  cen := fun _ => (Representation.trivial ℂ _ _).asAlgebraHom.comp (Subalgebra.val _)
  eOp := fun _ => 0
  eOp_idem := fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  eOp_sa := fun _ _ _ => by simp
  eOp_tie := fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  RR := zeroHLat D.what₂.LL
  RR_frames := (zeroHLat_good D.what₂.LL).1
  jEE := 0
  jEE_basis := ⟨by
    have : IsEmpty (zeroHLat D.what₂.LL).ι := inferInstanceAs (IsEmpty (Fin 0))
    exact linearIndependent_empty_type, Subsingleton.elim _ _⟩
  jEE_norm := fun x => (normAt_empty (ι := Fin 0) _ _ _ _).trans (by simp)

theorem rowSideZero_RRDef (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] [Subsingleton EE] : (rowSideZero D EE).RRDef := by
  intro x
  have hx : x = 0 := Subsingleton.elim (α := Fin 0 → D.what₂.LL) x 0
  rw [hx]
  exact ⟨fun _ w => ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [smul_zero]; exact Submodule.zero_mem _⟩, fun _ => Submodule.zero_mem _⟩

def trivialSide (D : D7) [Subsingleton D.what₂.EE0] : BaseLevelRowSide D := ⟨rowSideZero D D.what₂.EE0⟩

theorem trivialSide_rrDef_of_subsingleton (D : D7) [Subsingleton D.what₂.EE0] : (trivialSide D).s.RRDef := rowSideZero_RRDef D _

end Formalism.MainNotions.Inhab

end
