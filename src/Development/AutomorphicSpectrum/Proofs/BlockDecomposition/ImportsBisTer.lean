import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedVectorLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionFixedSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantHeckeKernel

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem c3 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C3 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ
  exact ⟨GlobalTheory.T.jacquet_projection_fixed_surjective k N h d hd J hJo hJc hJf hpos V π hπ.1,
    GlobalTheory.T.jacquet_fixed_vector_lift k N h d hd J hJo hJc hJf hpos V π hπ,
    GlobalTheory.T.strictly_dominant_hecke_kernel k N h d hd J hJo hJc hJf hpos V π hπ.1⟩

end GlobalTheory.CompanionTheory.Lbc
