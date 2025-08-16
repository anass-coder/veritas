qemu-system-x86_64  \
  -machine accel=kvm,type=q35 \
  -cpu host,+vmx \
  -smp 60 \
  -m 200G \
  -nographic \
  -snapshot \
  -device virtio-net-pci,netdev=net0 \
  -netdev user,id=net0,hostfwd=tcp::2222-:22 \
  -drive if=virtio,format=qcow2,file=./jammy-server-cloudimg-amd64-disk-kvm.img
