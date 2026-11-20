"""Unpack the verification archive and replay a requested PA theorem."""
import argparse
import hashlib
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile

def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('archive', type=Path, nargs='+', help='Main archive followed by any companion data volumes')
    cli.add_argument('--work', type=Path, required=True, help='New directory for sources and build output')
    cli.add_argument('--target', default='NF185PAInternalConsistency')
    cli.add_argument('--jobs', type=int, default=2)
    cli.add_argument('--sha256', action='append', help='Published archive SHA-256, repeated in archive order')
    cli.add_argument('--verify-only', action='store_true', help='Unpack, reconstruct missing certificates, verify hashes and check the machine bytes')
    args=cli.parse_args()
    if args.jobs<1:
        cli.error('--jobs must be positive')
    archives=[a.resolve() for a in args.archive]
    if args.sha256 and (len(args.sha256)!=len(archives) or any(hashlib.sha256(a.read_bytes()).hexdigest()!=h for a,h in zip(archives,args.sha256))):
        cli.error('The specified archive digests do not match the supplied files.')
    work=args.work.resolve()
    work.mkdir(parents=True,exist_ok=False)
    for archive in archives:
        with tarfile.open(archive,'r:xz') as tar:
            for item in tar:
                path=PurePosixPath(item.name)
                if path.is_absolute() or '..' in path.parts or not path.parts or path.parts[0]!='NF185_PA':
                    raise ValueError(f'Unexpected archive path: {item.name}')
                out=work.joinpath(*path.parts)
                if item.isdir():
                    out.mkdir(parents=True,exist_ok=True)
                elif item.isfile():
                    out.parent.mkdir(parents=True,exist_ok=True)
                    with tar.extractfile(item) as src,out.open('xb') as dst:
                        shutil.copyfileobj(src,dst)
                else:
                    raise ValueError(f'Unexpected special file {item.name}')
    root=work/'NF185_PA'
    subprocess.run([sys.executable,'replay.py','--verify-only','--jobs',str(args.jobs)],cwd=root,check=True)
    subprocess.run([sys.executable,'-B','verify.py'],cwd=root,check=True)
    if not args.verify_only:
        if not shutil.which('lake'):
            raise SystemExit('Install elan with the pinned Lean 4.35.0 toolchain to compile the checked sources.')
        subprocess.run(['lake','exe','cache','get'],cwd=root,check=True)
        subprocess.run(['lake','env',sys.executable,'replay.py','--target',args.target,'--jobs',str(args.jobs)],cwd=root,check=True)
if __name__=='__main__':
    main()
