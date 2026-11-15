// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Windows kernel file identities, including files no longer named by their path.

use std::{fs::File, io, os::windows::io::AsRawHandle};

#[repr(C)]
#[derive(Default)]
struct Information {
    volume: u64,
    file_id: [u8; 16],
}

#[link(name = "kernel32")]
unsafe extern "system" {
    fn GetFileInformationByHandleEx(
        file: *mut core::ffi::c_void,
        class: i32,
        information: *mut core::ffi::c_void,
        size: u32,
    ) -> i32;
}

pub(super) fn of(file: &File) -> io::Result<(u64, [u8; 16])> {
    let mut information = Information::default();
    // SAFETY: file retains a live handle and information has exactly the C
    // FILE_ID_INFO layout for FileIdInfo (18), writable for the supplied size.
    if unsafe {
        GetFileInformationByHandleEx(
            file.as_raw_handle(),
            18,
            (&raw mut information).cast(),
            std::mem::size_of::<Information>() as u32,
        )
    } == 0
    {
        return Err(io::Error::last_os_error());
    }
    checked(information)
}

fn checked(information: Information) -> io::Result<(u64, [u8; 16])> {
    if information.file_id == [0; 16] || information.file_id == [0xff; 16] {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "kernel file identity unavailable",
        ));
    }
    Ok((information.volume, information.file_id))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unavailable_file_ids_never_compare_as_an_identity() {
        for file_id in [[0; 16], [0xff; 16]] {
            assert_eq!(
                checked(Information { volume: 7, file_id })
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::Unsupported
            );
        }
        let file_id = [1; 16];
        assert_eq!(
            checked(Information { volume: 7, file_id }).unwrap(),
            (7, file_id)
        );
    }
}
