import os
import struct
import subprocess
import sys
import numpy as np
import pyarrow as pa
import pyarrow.parquet as pq


def load_large_string(off_path: str, data_path: str, n: int) -> pa.Array:
    if n == 0:
        return pa.array([], type=pa.string())
    off_buf = pa.memory_map(off_path, "r")
    data_size = os.path.getsize(data_path)
    data_buf = pa.memory_map(data_path, "r") if data_size > 0 else pa.py_buffer(b"")
    return pa.Array.from_buffers(pa.large_string(), n, [None, off_buf, data_buf])


def load_primitive(path: str, pa_type: pa.DataType, n: int) -> pa.Array:
    if n == 0:
        return pa.array([], type=pa_type)
    buf = pa.memory_map(path, "r")
    return pa.Array.from_buffers(pa_type, n, [None, buf])


def main() -> None:
    output_dir = os.environ.get("OUTPUT_DIR", "/output")
    scratch_dir = os.environ.get("SCRATCH_DIR", "/scratch")
    os.makedirs(os.path.join(output_dir, "user_daily"), exist_ok=True)
    os.makedirs(os.path.join(output_dir, "campaign_daily"), exist_ok=True)

    # 1. Run compiled C++ core engine
    res = subprocess.run(["/app/pipeline"], check=False)
    if res.returncode != 0:
        sys.exit(res.returncode)

    # 2. Read metadata & category dictionary
    with open(os.path.join(scratch_dir, "meta.bin"), "rb") as f:
        ud_rows, cd_rows = struct.unpack("<qq", f.read(16))

    cats = []
    with open(os.path.join(scratch_dir, "categories.bin"), "rb") as f:
        nc = struct.unpack("<I", f.read(4))[0]
        for _ in range(nc):
            length = struct.unpack("<I", f.read(4))[0]
            cats.append(f.read(length).decode("utf-8"))

    # 3. Build & write user_daily Parquet (zero-copy from binary arrays)
    if ud_rows == 0:
        ud_table = pa.table({
            "user_id": pa.array([], type=pa.string()),
            "day": pa.array([], type=pa.date32()),
            "sessions": pa.array([], type=pa.int64()),
            "events": pa.array([], type=pa.int64()),
            "revenue_cents": pa.array([], type=pa.int64()),
            "top_category": pa.array([], type=pa.string()),
        })
    else:
        cat_indices = np.fromfile(os.path.join(scratch_dir, "ud_cat.bin"), dtype=np.int32)
        mask = cat_indices < 0
        cat_dict = pa.array(cats, type=pa.string())
        idx_arr = pa.array(cat_indices, mask=mask, type=pa.int32())
        top_cat_arr = pa.DictionaryArray.from_arrays(idx_arr, cat_dict).cast(pa.string())

        ud_table = pa.table({
            "user_id": load_large_string(
                os.path.join(scratch_dir, "ud_uid_off.bin"),
                os.path.join(scratch_dir, "ud_uid_data.bin"),
                ud_rows,
            ),
            "day": load_primitive(os.path.join(scratch_dir, "ud_day.bin"), pa.date32(), ud_rows),
            "sessions": load_primitive(os.path.join(scratch_dir, "ud_sess.bin"), pa.int64(), ud_rows),
            "events": load_primitive(os.path.join(scratch_dir, "ud_ev.bin"), pa.int64(), ud_rows),
            "revenue_cents": load_primitive(os.path.join(scratch_dir, "ud_rev.bin"), pa.int64(), ud_rows),
            "top_category": top_cat_arr,
        })

    pq.write_table(
        ud_table,
        os.path.join(output_dir, "user_daily", "part-0.parquet"),
        compression="snappy",
    )

    # 4. Build & write campaign_daily Parquet
    if cd_rows == 0:
        cd_table = pa.table({
            "campaign_id": pa.array([], type=pa.string()),
            "channel": pa.array([], type=pa.string()),
            "day": pa.array([], type=pa.date32()),
            "sessions": pa.array([], type=pa.int64()),
            "purchasing_sessions": pa.array([], type=pa.int64()),
            "revenue_cents": pa.array([], type=pa.int64()),
            "assisted_sessions": pa.array([], type=pa.int64()),
        })
    else:
        cd_table = pa.table({
            "campaign_id": load_large_string(
                os.path.join(scratch_dir, "cd_cid_off.bin"),
                os.path.join(scratch_dir, "cd_cid_data.bin"),
                cd_rows,
            ),
            "channel": load_large_string(
                os.path.join(scratch_dir, "cd_ch_off.bin"),
                os.path.join(scratch_dir, "cd_ch_data.bin"),
                cd_rows,
            ),
            "day": load_primitive(os.path.join(scratch_dir, "cd_day.bin"), pa.date32(), cd_rows),
            "sessions": load_primitive(os.path.join(scratch_dir, "cd_sess.bin"), pa.int64(), cd_rows),
            "purchasing_sessions": load_primitive(os.path.join(scratch_dir, "cd_psess.bin"), pa.int64(), cd_rows),
            "revenue_cents": load_primitive(os.path.join(scratch_dir, "cd_rev.bin"), pa.int64(), cd_rows),
            "assisted_sessions": load_primitive(os.path.join(scratch_dir, "cd_assist.bin"), pa.int64(), cd_rows),
        })

    pq.write_table(
        cd_table,
        os.path.join(output_dir, "campaign_daily", "part-0.parquet"),
        compression="snappy",
    )


if __name__ == "__main__":
    main()