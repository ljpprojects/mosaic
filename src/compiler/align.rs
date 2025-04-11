//! "Top notch" alignment data for supported architectures to use in the compiler.
//! ## Sources
//! * https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms
//! * https://student.cs.uwaterloo.ca/~cs452/docs/rpi4b/aapcs64.pdf
//! * https://developer.arm.com/documentation/dui0472/m/C-and-C---Implementation-Details/Basic-data-types-in-ARM-C-and-C--
//! * https://en.wikipedia.org/wiki/Data_structure_alignment#Typical_alignment_of_C_structs_on_x86
//! * https://wiki.debian.org/ArchitectureSpecificsMemo#via_a_special_tool
//! * https://d3s.mff.cuni.cz/files/teaching/nswi200/202324/doc/riscv-abi.pdf

use target_lexicon::{Aarch64Architecture, Architecture, ArmArchitecture, CDataModel, Triple};
use crate::compiler::cranelift::types::CraneliftType;
use crate::ternary;

/// Given a Cranelift backend type and an architecture, get the alignment of that type on that architecture with reasonable accuracy.
/// Returns null when given CraneliftType::Any or CraneliftType::Generic or an unsupported architecture/data model.
pub fn alignment_of_cranelift_type_on_architecture(ty: &CraneliftType, triple: &Triple) -> Option<u8> {
    match (triple.architecture, triple.data_model().ok()?) {
        (Architecture::X86_64, CDataModel::LP64) | (Architecture::Riscv64(..), CDataModel::LP64) | (Architecture::S390x, _) | (Architecture::Aarch64(Aarch64Architecture::Aarch64), _) => match ty {
            CraneliftType::Any | CraneliftType::Generic(..) => None,
            CraneliftType::Int8 | CraneliftType::UInt8 | CraneliftType::Null | CraneliftType::Bool => Some(1),
            CraneliftType::Int16 | CraneliftType::UInt16 => Some(2),
            CraneliftType::Int32 | CraneliftType::UInt32 => Some(4),
            CraneliftType::Int64 | CraneliftType::UInt64 => Some(8),
            CraneliftType::Float32 => Some(4),
            CraneliftType::Float64 => Some(8),
            CraneliftType::FuncPtr { .. } => Some(8),
            CraneliftType::DataPtr(_) => Some(8),
            CraneliftType::CPtr(_, _, _) => Some(8),
            CraneliftType::FatPtr(_, _, _) => Some(8),
            CraneliftType::Slice(_, _, _, _) => Some(8),
        }
        _ => None,
    }
}

/// Given the alignments and sizes of fields in a data declaration, returns the following in order:
/// * Total size
/// * Offsets of each field (in order)
pub fn calculate_data_cranelift(field_alignments: &[u8], field_sizes: &[u8]) -> (u16, Vec<u16>) {
    if field_alignments.len() == 0 {
        return (0, vec![]);
    }
    
    let mut current_offset: u16 = 0;
    let max_alignment = *field_alignments.iter().max().unwrap();

    let mut field_offsets = vec![];
    field_offsets.reserve(field_sizes.len());

    for (alignment, size) in field_alignments.iter().zip(field_sizes.iter()) {
        current_offset += ternary!(current_offset % *alignment as u16 == 0 => 0; *alignment as u16 - (current_offset % *alignment as u16)) + *size as u16;
        field_offsets.push(current_offset - *size as u16);
    }

    (
        current_offset + ternary!(current_offset % max_alignment as u16 == 0 => 0; max_alignment as u16 - (current_offset % max_alignment as u16)),
        field_offsets,
    )
}

mod tests {
    use target_lexicon::Triple;
    use crate::compiler::align::{alignment_of_cranelift_type_on_architecture, calculate_data_cranelift};
    use crate::compiler::cranelift::types::CraneliftType;
    use crate::utils::Indirection;

    #[test]
    fn test_alignment_of_types() {
        let types = &[
            CraneliftType::Int16,
            CraneliftType::Slice(Indirection::new(CraneliftType::UInt32), 13, false, false),
            CraneliftType::Float32,
            CraneliftType::Bool,
            CraneliftType::Slice(Indirection::new(CraneliftType::UInt8), 13, false, false),
            CraneliftType::Float64,
        ];

        for ty in types {
            println!("{:?}", alignment_of_cranelift_type_on_architecture(&ty, &Triple::host()));
        }

        let mut alignments = types.iter().map(|t| alignment_of_cranelift_type_on_architecture(&t, &Triple::host()).unwrap()).collect::<Vec<_>>();

        alignments.sort();
        
        println!("{:?}", alignments);
        println!("{:#?}", calculate_data_cranelift(&*alignments, &*alignments));
    }
}