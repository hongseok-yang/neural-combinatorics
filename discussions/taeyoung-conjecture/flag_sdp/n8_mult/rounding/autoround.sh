#!/bin/zsh
# after each new face2 chunk, attempt the exact rounding; stop on success.
cd "$(dirname "$0")"
last=""
while true; do
  if [ -f data/result_face2.pkl ]; then
    cur=$(stat -f %m data/result_face2.pkl)
    if [ "$cur" != "$last" ]; then
      last=$cur
      echo "=== $(date '+%H:%M:%S') new face2 iterate; rounding attempt ==="
      nice -n 18 python3 step6b_iterate.py --src data/result_face2.pkl \
        --tag certificate --max-rounds 4 2>&1 | tail -20
      if [ -f data/certificate.pkl ]; then
        echo "=== CERTIFICATE PRODUCED; running standalone verifier ==="
        nice -n 18 python3 verify_exact.py data/certificate.pkl 2>&1 | tail -8
        exit 0
      fi
    fi
  fi
  sleep 120
done
