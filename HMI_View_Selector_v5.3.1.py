#!/usr/bin/env python3


import json
import os
import re
import shutil
import subprocess
import threading
import time
import tkinter as tk
from tkinter import messagebox, ttk
import configparser
import hashlib  # For secure password hashing
from concurrent.futures import ThreadPoolExecutor
from pymodbus.client import ModbusTcpClient
import paramiko  # For SSH functionality
from datetime import datetime

# Software version and metadata
__version__ = "5.3.1"
__author__ = "Jeirmey Burnside" "of Burnside Industries"
__license__ = "MIT"
__status__ = "Production"


class HoverButton(tk.Button):
    def __init__(self, master=None, hover_color=None, **kwargs):
        super().__init__(master, **kwargs)
        self.default_color = kwargs.get('bg', 'SystemButtonFace')
        self.hover_color = hover_color or self.default_color
        self.bind("<Enter>", self.on_enter)
        self.bind("<Leave>", self.on_leave)

    def on_enter(self, e):
        super().config(bg=self.hover_color)

    def on_leave(self, e):
        super().config(bg=self.default_color)
    
    def config(self, **kwargs):
        # Update default_color when bg is changed (but not during hover events)
        if 'bg' in kwargs:
            self.default_color = kwargs['bg']
        super().config(**kwargs)


class ModernApp:
    def __init__(self, root):
        self.root = root
        
        # Configure the main window
        self.root.title("HMI View Selector v5.2.1")
        self.root.configure(bg='#1e1e1e')
        
        # Dark style theme
        self.bg_color = '#1e1e1e'
        self.btn_color = '#0078d4'
        self.text_color = 'white'
        self.highlight_color = '#2b88d8'
        
        # Initialize frames
        self.current_frame = None
        self.content_frame = None
        
        # Auto-control feature toggle
        self.auto_control_active = False
        self.auto_threshold = 1050  # Turbo temp threshold for auto-control activation
        self.monitoring_active = False
        self.monitor_threads = []  # Initialize monitor threads list
        self.was_monitoring_before_navigation = False  # Track monitoring state across page transitions
        
        # Preload units info container
        self.units_info = []
        
        # Auto fan control timing - track last fan activation time per unit
        self.last_fan_activation = {}  # Dictionary to store last activation time per unit IP
        
        # IP range configuration - default values
        self.ip_start = [10, 55, 10, 100]
        self.ip_end = [10, 55, 10, 255]
        self.load_ip_config()
        
        # Maintenance mode settings
        self.maintenance_mode_active = False
        self.turbo_temp_threshold = 1050  # Default threshold
        
        # User management settings
        self.users = {}  # Will store user data with roles
        self.current_user = None  # Currently logged in user
        self.current_user_role = None  # Current user's role
        self.maintenance_password = ""  # Legacy support
        self.ip_setup_password = ""    # Legacy support
        self.activity_log = []  # Activity log for tracking changes
        self.master_maintenance_mode = False  # Master maintenance mode for global SP control
        self.load_user_config()  # Load user configuration from config file
        self.load_activity_log()  # Load activity log
        
        # Synchronize maintenance_mode_active with master maintenance mode on startup
        if self.master_maintenance_mode:
            self.maintenance_mode_active = True
        
        # Initialize variables
        self.exe_folder = "Digi_Prime_HMIs"
        self.exe_files = self.get_exe_files()
        self.pump_assignments = self.load_assignments()
        
        # Load logo
        self.logo = tk.PhotoImage(file='Logo.png')

        # Style configuration
        self.style = ttk.Style()
        self.style.theme_use('clam')  # Modern theme
        
        # Configure modern styles
        self.style.configure('Custom.TFrame', background='#1e1e1e')
        self.style.configure('Custom.TLabel', 
                           background='#1e1e1e', 
                           foreground='#ffffff', 
                           font=('Segoe UI', 12))
        self.style.configure('Custom.TButton', 
                           font=('Segoe UI', 12),
                           background='#0078d4',
                           foreground='white')
        
        # Configure Combobox style
        self.style.configure('TCombobox',
                           fieldbackground='#2d2d2d',
                           background='#0078d4',
                           foreground='white',
                           arrowcolor='white',
                           selectbackground='#0078d4',
                           selectforeground='white')
        
        self.style.map('TCombobox',
                      fieldbackground=[('readonly', '#2d2d2d')],
                      selectbackground=[('readonly', '#0078d4')],
                      selectforeground=[('readonly', 'white')])

        self.create_ini_page()

    def create_ini_page(self):
        if self.current_frame:
            self.current_frame.destroy()

        # Logo at the top
        logo_label = tk.Label(self.root, image=self.logo, bg='#1e1e1e')
        logo_label.pack(pady=5)

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True)

        # Modern styled buttons with hover effect
        submit_button = HoverButton(
            self.current_frame,
            text="Open Viewer Program",
            command=self.load_existing_configuration,
            font=("Segoe UI", 14),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#2b88d8"  # Lighter blue on hover
        )
        submit_button.grid(row=1, column=0, pady=15, ipadx=10, ipady=5)

        back_button = HoverButton(
            self.current_frame,
            text="New Site",
            command=self.first_scan,
            font=("Segoe UI", 14),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#e85b24"  # Lighter red on hover
        )
        back_button.grid(row=2, column=0, pady=15, ipadx=10, ipady=5)

        ip_setup_button = HoverButton(
            self.current_frame,
            text="IP Setup",
            command=self.create_ip_setup_password_page,
            font=("Segoe UI", 14),
            bg="#6b69d6",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#7b79e6"  # Lighter purple on hover
        )
        ip_setup_button.grid(row=3, column=0, pady=15, ipadx=10, ipady=5)

    def create_ini_page2(self):
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True)

        # Modern styled buttons with hover effect
        submit_button = HoverButton(
            self.current_frame,
            text="Open Viewer Program",
            command=self.load_existing_configuration,
            font=("Segoe UI", 14),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#2b88d8"  # Lighter blue on hover
        )
        submit_button.grid(row=1, column=0, pady=15, ipadx=10, ipady=5)

        back_button = HoverButton(
            self.current_frame,
            text="New Site",
            command=self.first_scan,
            font=("Segoe UI", 14),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#e85b24"  # Lighter red on hover
        )
        back_button.grid(row=2, column=0, pady=15, ipadx=10, ipady=5)

        ip_setup_button = HoverButton(
            self.current_frame,
            text="IP Setup",
            command=self.create_ip_setup_password_page,
            font=("Segoe UI", 14),
            bg="#6b69d6",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#7b79e6"  # Lighter purple on hover
        )
        ip_setup_button.grid(row=3, column=0, pady=15, ipadx=10, ipady=5)

    def create_ini2(self):
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True)

        header_label = tk.Label(
            self.current_frame,
            text="Enter Number of Pumps",
            font=("Segoe UI", 22, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.grid(row=0, column=0, pady=5)

        # Modern entry field
        entry_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        entry_frame.grid(row=1, column=0, pady=15)
        
        self.pump_input = tk.Entry(
            entry_frame,
            font=("Segoe UI", 16),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            justify='center',
            width=10
        )
        self.pump_input.pack(ipady=5)

        # Modern continue button with hover effect
        start_button = HoverButton(
            self.current_frame,
            text="Continue",
            command=self.create_columns,
            font=("Segoe UI", 14),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#2b88d8",  # Lighter blue on hover
        )
        start_button.grid(row=3, column=0, pady=20, ipady=5)

    def create_columns(self):
        try:
            num_pumps = int(self.pump_input.get())
            if num_pumps <= 48:
                self.create_main_page2(num_pumps)
            else:
                messagebox.showerror("Invalid Input", "Please enter a valid number (maximum 48 pumps).")
        except ValueError:
            messagebox.showerror("Invalid Input", "Please enter a valid number.")

    def create_main_page(self, num_pumps):
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root)
        self.current_frame.configure(bg='#1e1e1e')
        self.current_frame.pack(expand=True, fill='both', padx=30, pady=20)

        # Modern header with subtle bottom border
        header_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        header_frame.pack(fill='x', pady=(0, 5))
        
        header_label = tk.Label(
            header_frame,
            text="HMI View Selector",
            font=("Segoe UI", 26, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.pack(pady=(0, 5))
        
        separator = ttk.Separator(header_frame, orient='horizontal')
        separator.pack(fill='x', padx=50)

        # Create a frame for the pumps grid with modern styling
        grid_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        grid_frame.pack(expand=True, fill='both')

        # Update exe files
        self.exe_files = self.get_exe_files()
        exe_names = [os.path.basename(file)[:-4] for file in self.exe_files]

        # Calculate rows and columns
        rows = (num_pumps + 1) // 2

        for i in range(num_pumps):
            # Calculate position
            col_offset = 0 if i < rows else 4
            row_index = i % rows

            # Create modern pump controls
            pump_label = tk.Label(
                grid_frame,
                text=f"Pump {i + 1}",
                font=("Segoe UI", 12, "bold"),
                bg='#1e1e1e',
                fg='white'
            )
            pump_label.grid(row=row_index, column=col_offset, sticky='e', padx=10, pady=8)

            # Modern styled dropdown
            dropdown = ttk.Combobox(
                grid_frame,
                values=["Select Pump"] + exe_names,
                state="readonly",
                width=18,
                font=("Segoe UI", 11)
            )

            if i in self.pump_assignments and "exe_name" in self.pump_assignments[i]:
                dropdown.set(self.pump_assignments[i]["exe_name"])
            else:
                dropdown.set("Select Pump")

            dropdown.grid(row=row_index, column=col_offset + 1, padx=10, pady=8)

            # Modern styled run button with hover effect
            run_button = HoverButton(
                grid_frame,
                text="HMI",
                width=6,
                font=("Segoe UI", 11, "bold"),
                bg='#107c10',
                fg='white',
                relief='flat',
                hover_color='#0ea10e',  # Lighter green on hover
                command=lambda i=i, d=dropdown: self.set_pump_assignment(i, d)
            )
            run_button.grid(row=row_index, column=col_offset + 2, padx=10, pady=8)

            # Store the new widgets in pump_assignments
            self.pump_assignments[i] = {
                "dropdown": dropdown,
                "run_button": run_button,
                "exe_name": self.pump_assignments.get(i, {}).get("exe_name", "Select Pump")
            }

        # Modern styled bottom control buttons
        button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        button_frame.pack(side='bottom', pady=25)

        scan_button = HoverButton(
            button_frame,
            text="Scan",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#0078d4",
            fg="white",
            relief="flat",
            hover_color="#2b88d8",  # Lighter blue on hover
            command=self.scan_ip2
        )
        scan_button.pack(side='left', padx=10, ipady=5)
        
        # Monitor button for the new page
        monitor_button = HoverButton(
            button_frame,
            text="Turbo Monitor",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#d83b01",
            fg="white",
            relief="flat",
            hover_color="#e85b24",  # Lighter red on hover
            command=self.create_monitor_page
        )
        monitor_button.pack(side='left', padx=10, ipady=5)
        
        # Operations button
        # operations_button = HoverButton(
        #     button_frame,
        #     text="Operations",
        #     width=15,
        #     font=("Segoe UI", 12, "bold"),
        #     bg="#6b69d6",
        #     fg="white",
        #     relief="flat",
        #     hover_color="#7b79e6",  # Lighter purple on hover
        #     command=self.create_operations_page
        # )
        # operations_button.pack(side='left', padx=10, ipady=5)

    def create_main_page2(self, num_pumps):
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root)
        self.current_frame.configure(bg='#1e1e1e')
        self.current_frame.pack(expand=True, fill='both', padx=30, pady=20)

        # Modern header with subtle bottom border
        header_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        header_frame.pack(fill='x', pady=(0, 5))
        
        header_label = tk.Label(
            header_frame,
            text="HMI SWITCH",
            font=("Segoe UI", 26, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.pack(pady=(0, 5))
        
        separator = ttk.Separator(header_frame, orient='horizontal')
        separator.pack(fill='x', padx=50)

        # Create a frame for the pumps grid with modern styling
        grid_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        grid_frame.pack(expand=True, fill='both')

        # Update exe files
        self.exe_files = self.get_exe_files()
        exe_names = [os.path.basename(file)[:-4] for file in self.exe_files]

        # Calculate number of columns needed (max 12 pumps per column)
        num_columns = (num_pumps + 11) // 12
        pumps_per_column = min(12, (num_pumps + num_columns - 1) // num_columns)

        for i in range(num_pumps):
            # Calculate position (column first, then row)
            column = i // pumps_per_column
            row = i % pumps_per_column
            col_offset = column * 4  # Each column group takes 4 grid columns

            # Create modern pump controls
            pump_label = tk.Label(
                grid_frame,
                text=f"Pump {i + 1}",
                font=("Segoe UI", 12, "bold"),
                bg='#1e1e1e',
                fg='white'
            )
            pump_label.grid(row=row, column=col_offset, sticky='e', padx=10, pady=8)

            # Modern styled dropdown
            dropdown = ttk.Combobox(
                grid_frame,
                values=["Select Pump"] + exe_names,
                state="readonly",
                width=18,
                font=("Segoe UI", 11)
            )

            dropdown.set("Select Pump")

            dropdown.grid(row=row, column=col_offset + 1, padx=10, pady=8)

            # Modern styled run button with hover effect
            run_button = HoverButton(
                grid_frame,
                text="HMI",
                width=10,
                font=("Segoe UI", 11, "bold"),
                bg='#107c10',
                fg='white',
                relief='flat',
                hover_color='#0ea10e',  # Lighter green on hover
                command=lambda i=i, d=dropdown: self.set_pump_assignment(i, d)
            )
            run_button.grid(row=row, column=col_offset + 2, padx=10, pady=8)

            self.pump_assignments[i] = {"dropdown": dropdown, "run_button": run_button}

        # Modern styled bottom control buttons
        button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        button_frame.pack(side='bottom', pady=25)

        scan_button = HoverButton(
            button_frame,
            text="Scan",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#0078d4",
            fg="white",
            relief="flat",
            hover_color="#2b88d8",  # Lighter blue on hover
            command=self.scan_ip
        )
        scan_button.pack(side='left', padx=10, ipady=5)
        
        # Monitor button for the new page
        monitor_button = HoverButton(
            button_frame,
            text="Monitor",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#d83b01",
            fg="white",
            relief="flat",
            hover_color="#e85b24",  # Lighter red on hover
            command=self.create_monitor_page
        )
        monitor_button.pack(side='left', padx=10, ipady=5)
        
        # Operations button
        # operations_button = HoverButton(
        #     button_frame,
        #     text="Operations",
        #     width=15,
        #     font=("Segoe UI", 12, "bold"),
        #     bg="#6b69d6",
        #     fg="white",
        #     relief="flat",
        #     hover_color="#7b79e6",  # Lighter purple on hover
        #     command=self.create_operations_page
        # )
        # operations_button.pack(side='left', padx=10, ipady=5)

    def first_scan(self):
        # Delete Digi_Prime_HMIs folder before scanning
        folder_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "Digi_Prime_HMIs")
        if os.path.exists(folder_path):
            try:
                shutil.rmtree(folder_path)
                print(f"Successfully deleted {folder_path}")
            except Exception as e:
                print(f"Error deleting {folder_path}: {e}")
        
        threading.Thread(target=self.scan_ip, daemon=True).start()

    def scan_ip(self):
        # Delete Digi_Prime_HMIs folder before scanning
        folder_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "Digi_Prime_HMIs")
        if os.path.exists(folder_path):
            try:
                shutil.rmtree(folder_path)
                print(f"Successfully deleted {folder_path}")
            except Exception as e:
                print(f"Error deleting {folder_path}: {e}")
                messagebox.showerror("Error", f"Failed to delete Digi_Prime_HMIs folder: {e}")
                return
        
        # Verify folder is deleted before proceeding
        if os.path.exists(folder_path):
            messagebox.showerror("Error", "Failed to delete Digi_Prime_HMIs folder. Cannot proceed with scan.")
            return
        
        print("Verified: Digi_Prime_HMIs folder successfully removed")
                
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack()
        progress_bar = ttk.Progressbar(self.current_frame, length=400, mode='determinate')
        progress_bar.pack(pady=10)
        progress_label = tk.Label(self.current_frame, text="Scanning IP addresses...",
                                  font=("Segoe UI", 20, "bold"), bg='#1e1e1e', fg='white')
        progress_label.pack(pady=10)



        # Calculate IP range based on configuration
        start_ip_base = f"{self.ip_start[0]}.{self.ip_start[1]}.{self.ip_start[2]}"
        start_last_octet = self.ip_start[3]
        end_last_octet = self.ip_end[3]
        
        def scan_single_ip(i):
            ip = f"{start_ip_base}.{i}"
            client = ModbusTcpClient(ip)
            try:
                if client.connect():
                    string_result = client.read_holding_registers( address=128, count=10)
                    int_result = client.read_holding_registers( address=138, count=1)
                    if not (string_result.isError() or int_result.isError()):
                        self.process_scan_results(string_result, int_result, ip)
            except Exception as e:
                print(f"Error scanning {ip}: {e}")
            finally:
                client.close()

        def run_scan():
            ip_range = list(range(start_last_octet, end_last_octet + 1))
            total_ips = len(ip_range)
            with ThreadPoolExecutor(max_workers=20) as executor:
                for i, _ in enumerate(executor.map(scan_single_ip, ip_range)):
                    progress = (i + 1) / total_ips * 100
                    progress_bar['value'] = progress
                    self.current_frame.update()

            self.current_frame.destroy()
            self.create_ini2()

        threading.Thread(target=run_scan, daemon=True).start()

    def scan_ip2(self):
        # Delete Digi_Prime_HMIs folder before scanning
        folder_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "Digi_Prime_HMIs")
        if os.path.exists(folder_path):
            try:
                shutil.rmtree(folder_path)
                print(f"Successfully deleted {folder_path}")
            except Exception as e:
                print(f"Error deleting {folder_path}: {e}")
                messagebox.showerror("Error", f"Failed to delete Digi_Prime_HMIs folder: {e}")
                return
        
        # Verify folder is deleted before proceeding
        if os.path.exists(folder_path):
            messagebox.showerror("Error", "Failed to delete Digi_Prime_HMIs folder. Cannot proceed with scan.")
            return
        
        print("Verified: Digi_Prime_HMIs folder successfully removed")
        
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack()
        progress_bar = ttk.Progressbar(self.current_frame, length=400, mode='determinate')
        progress_bar.pack(pady=10)
        progress_label = tk.Label(self.current_frame, text="Scanning IP addresses...",
                                  font=("Segoe UI", 20, "bold"), bg='#1e1e1e', fg='white')
        progress_label.pack(pady=10)



        # Calculate IP range based on configuration
        start_ip_base = f"{self.ip_start[0]}.{self.ip_start[1]}.{self.ip_start[2]}"
        start_last_octet = self.ip_start[3]
        end_last_octet = self.ip_end[3]
        
        def scan_single_ip(i):
            ip = f"{start_ip_base}.{i}"
            client = ModbusTcpClient(ip)
            try:
                if client.connect():
                    string_result = client.read_holding_registers(address=128, count=10)
                    int_result = client.read_holding_registers(address=138, count=1)
                    if not (string_result.isError() or int_result.isError()):
                        self.process_scan_results(string_result, int_result, ip)
            except Exception as e:
                print(f"Error scanning {ip}: {e}")
            finally:
                client.close()

        def run_scan():
            ip_range = list(range(start_last_octet, end_last_octet + 1))
            total_ips = len(ip_range)
            with ThreadPoolExecutor(max_workers=16) as executor:
                for i, _ in enumerate(executor.map(scan_single_ip, ip_range)):
                    progress = (i + 1) / total_ips * 100
                    progress_bar['value'] = progress
                    self.current_frame.update()

            self.current_frame.destroy()
            self.load_existing_configuration()

        threading.Thread(target=run_scan, daemon=True).start()

    def create_ip_setup_page(self):
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True)

        # Header
        header_label = tk.Label(
            self.current_frame,
            text="IP Range Setup",
            font=("Segoe UI", 22, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.grid(row=0, column=0, columnspan=4, pady=20)

        # Start IP Range Section
        start_label = tk.Label(
            self.current_frame,
            text="Start IP Range:",
            font=("Segoe UI", 14, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        start_label.grid(row=1, column=0, columnspan=4, pady=(20, 10))

        # Start IP input fields
        self.start_ip_entries = []
        for i in range(4):
            entry = tk.Entry(
                self.current_frame,
                font=("Segoe UI", 12),
                bg='#2d2d2d',
                fg='white',
                insertbackground='white',
                relief='flat',
                justify='center',
                width=5
            )
            entry.grid(row=2, column=i, padx=5, pady=5)
            entry.insert(0, str(self.ip_start[i]))
            self.start_ip_entries.append(entry)
            
            if i < 3:
                dot_label = tk.Label(
                    self.current_frame,
                    text=".",
                    font=("Segoe UI", 14, "bold"),
                    bg='#1e1e1e',
                    fg='white'
                )
                dot_label.grid(row=2, column=i, sticky='e', padx=(25, 0))

        # End IP Range Section
        end_label = tk.Label(
            self.current_frame,
            text="End IP Range:",
            font=("Segoe UI", 14, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        end_label.grid(row=3, column=0, columnspan=4, pady=(30, 10))

        # End IP input fields
        self.end_ip_entries = []
        for i in range(4):
            entry = tk.Entry(
                self.current_frame,
                font=("Segoe UI", 12),
                bg='#2d2d2d',
                fg='white',
                insertbackground='white',
                relief='flat',
                justify='center',
                width=5
            )
            entry.grid(row=4, column=i, padx=5, pady=5)
            entry.insert(0, str(self.ip_end[i]))
            self.end_ip_entries.append(entry)
            
            if i < 3:
                dot_label = tk.Label(
                    self.current_frame,
                    text=".",
                    font=("Segoe UI", 14, "bold"),
                    bg='#1e1e1e',
                    fg='white'
                )
                dot_label.grid(row=4, column=i, sticky='e', padx=(25, 0))

        # Buttons
        button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        button_frame.grid(row=5, column=0, columnspan=4, pady=30)

        save_button = HoverButton(
            button_frame,
            text="Save",
            command=self.save_ip_config,
            font=("Segoe UI", 14),
            bg="#107c10",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#25902a"
        )
        save_button.pack(side='left', padx=10, ipady=5)

        cancel_button = HoverButton(
            button_frame,
            text="Cancel",
            command=self.create_ini_page2,
            font=("Segoe UI", 14),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#e85b24"
        )
        cancel_button.pack(side='left', padx=10, ipady=5)

    def save_ip_config(self):
        try:
            # Validate and save IP ranges
            start_ip = []
            end_ip = []
            
            # Enhanced IPv4 validation for start IP
            for i, entry in enumerate(self.start_ip_entries):
                value_str = entry.get().strip()
                # Check if entry is empty or not a valid number
                if not value_str or not value_str.isdigit():
                    messagebox.showerror("Invalid Input", f"Start IP octet {i+1} must be a valid number (received '{value_str}')")
                    return
                
                value = int(value_str)
                if not (0 <= value <= 255):
                    messagebox.showerror("Invalid Input", f"Start IP octet {i+1} must be between 0 and 255")
                    return
                start_ip.append(value)
            
            # Enhanced IPv4 validation for end IP
            for i, entry in enumerate(self.end_ip_entries):
                value_str = entry.get().strip()
                # Check if entry is empty or not a valid number
                if not value_str or not value_str.isdigit():
                    messagebox.showerror("Invalid Input", f"End IP octet {i+1} must be a valid number (received '{value_str}')")
                    return
                
                value = int(value_str)
                if not (0 <= value <= 255):
                    messagebox.showerror("Invalid Input", f"End IP octet {i+1} must be between 0 and 255")
                    return
                end_ip.append(value)
            
            # Validate that start IP is less than or equal to end IP
            start_ip_int = (start_ip[0] << 24) + (start_ip[1] << 16) + (start_ip[2] << 8) + start_ip[3]
            end_ip_int = (end_ip[0] << 24) + (end_ip[1] << 16) + (end_ip[2] << 8) + end_ip[3]
            
            # Format IP addresses for display
            start_ip_str = f"{start_ip[0]}.{start_ip[1]}.{start_ip[2]}.{start_ip[3]}"
            end_ip_str = f"{end_ip[0]}.{end_ip[1]}.{end_ip[2]}.{end_ip[3]}"
            
            if start_ip_int > end_ip_int:
                messagebox.showerror("Invalid Range", f"Start IP ({start_ip_str}) must be less than or equal to End IP ({end_ip_str})")
                return
            
            # Save the configuration
            self.ip_start = start_ip
            self.ip_end = end_ip
            
            # Save to file
            ip_config = {
                "ip_start": self.ip_start,
                "ip_end": self.ip_end
            }
            
            with open('ip_config.json', 'w') as f:
                json.dump(ip_config, f)
            
            # Log the IP configuration change
            self.log_activity("IP Configuration", f"IP range updated: {start_ip_str} to {end_ip_str}")
            
            messagebox.showinfo("Success", "IP configuration saved successfully!")
            self.create_ini_page2()
            
        except ValueError:
            messagebox.showerror("Invalid Input", "Please enter valid numbers for all IP octets")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save IP configuration: {e}")

    def load_ip_config(self):
        try:
            if os.path.exists('ip_config.json'):
                with open('ip_config.json', 'r') as f:
                    config = json.load(f)
                    self.ip_start = config.get('ip_start', [10, 55, 10, 100])
                    self.ip_end = config.get('ip_end', [10, 55, 10, 255])
        except Exception as e:
            print(f"Error loading IP configuration: {e}")
            # Use default values if loading fails
            self.ip_start = [10, 55, 10, 100]
            self.ip_end = [10, 55, 10, 255]
            
    def safe_widget_update(self, widget, **kwargs):
        """
        Safely update a widget's configuration, checking if it still exists
        """
        try:
            if widget and widget.winfo_exists():
                widget.config(**kwargs)
        except tk.TclError:
            # Widget has been destroyed, ignore the update
            pass
        except Exception as e:
            # Log other unexpected errors but don't crash
            print(f"Error updating widget: {e}")
    
    def bind_click_recursive(self, widget, callback):
        """
        Recursively bind click events to widget and all its children
        This makes the entire unit box clickable, not just empty spaces
        Excludes buttons and entry widgets to preserve their functionality
        """
        try:
            # Skip binding for buttons and entry widgets
            widget_class = widget.winfo_class()
            if widget_class not in ('Button', 'Entry'):
                widget.bind('<Button-1>', callback)
                for child in widget.winfo_children():
                    self.bind_click_recursive(child, callback)
        except Exception as e:
            print(f"Error binding click event: {e}")

    def hash_password(self, password):
        """
        Create a SHA-256 hash of the password
        """
        return hashlib.sha256(password.encode('utf-8')).hexdigest()
    
    def verify_password(self, input_password, stored_hash):
        """
        Verify if the input password matches the stored hash
        """
        return self.hash_password(input_password) == stored_hash
    
    def load_user_config(self):
        """
        Load user configuration from config.json file
        If file doesn't exist, create it with default admin user
        """
        config_file = 'config.json'
        
        # Default configuration with admin user and legacy passwords
        default_config = {
            "users": {
                "admin": {
                    "password_hash": self.hash_password("LBRT123!"),
                    "role": "admin",
                    "active": True,
                    "created_date": "2025-01-01"
                }
            },
            "maintenance_password": self.hash_password("LBRT123!"),  # Legacy support
            "ip_setup_password": self.hash_password("LBRT123!"),    # Legacy support
            "master_maintenance_mode": False,  # Default master maintenance mode state
            "turbo_temp_threshold": 1050  # Default turbo temperature threshold
        }
        
        try:
            if os.path.exists(config_file):
                with open(config_file, 'r') as f:
                    config = json.load(f)
                
                # Load users if present, otherwise use default
                self.users = config.get("users", default_config["users"])
                
                # Load legacy passwords for backward compatibility
                self.maintenance_password = config.get("maintenance_password", default_config["maintenance_password"])
                self.ip_setup_password = config.get("ip_setup_password", default_config["ip_setup_password"])
                
                # Load master maintenance mode state
                self.master_maintenance_mode = config.get("master_maintenance_mode", default_config["master_maintenance_mode"])
                
                # Load turbo temperature threshold
                self.turbo_temp_threshold = config.get("turbo_temp_threshold", default_config["turbo_temp_threshold"])
                
                # If no users exist, add default admin
                if not self.users:
                    self.users = default_config["users"]
                    self.save_user_config()
            else:
                # Create new config file with defaults
                with open(config_file, 'w') as f:
                    json.dump(default_config, f, indent=4)
                
                self.users = default_config["users"]
                self.maintenance_password = default_config["maintenance_password"]
                self.ip_setup_password = default_config["ip_setup_password"]
                self.master_maintenance_mode = default_config["master_maintenance_mode"]
                self.turbo_temp_threshold = default_config["turbo_temp_threshold"]
                
        except Exception as e:
            print(f"Error loading user configuration: {e}")
            # Use default values if loading fails
            self.users = default_config["users"]
            self.maintenance_password = default_config["maintenance_password"]
            self.ip_setup_password = default_config["ip_setup_password"]
            self.master_maintenance_mode = default_config["master_maintenance_mode"]
            self.turbo_temp_threshold = default_config["turbo_temp_threshold"]
    
    def save_user_config(self):
        """
        Save current user configuration to config.json file
        """
        config_file = 'config.json'
        
        config = {
            "users": self.users,
            "maintenance_password": self.maintenance_password,  # Legacy support
            "ip_setup_password": self.ip_setup_password,       # Legacy support
            "master_maintenance_mode": self.master_maintenance_mode,  # Persistent master maintenance mode
            "turbo_temp_threshold": self.turbo_temp_threshold  # Persistent turbo temperature threshold
        }
        
        try:
            with open(config_file, 'w') as f:
                json.dump(config, f, indent=4)
            return True
        except Exception as e:
            print(f"Error saving user configuration: {e}")
            return False
    
    def authenticate_user(self, username, password):
        """
        Authenticate a user and return their role if successful
        """
        if username in self.users:
            user_data = self.users[username]
            if user_data.get("active", True) and self.verify_password(password, user_data["password_hash"]):
                self.current_user = username
                self.current_user_role = user_data["role"]
                return user_data["role"]
        return None
    
    def create_user(self, username, password, role, created_by_admin=True):
        """
        Create a new user with specified role
        """
        if not created_by_admin and self.current_user_role != "admin":
            return False, "Only administrators can create users"
        
        if username in self.users:
            return False, "Username already exists"
        
        if role not in ["admin", "tech"]:
            return False, "Invalid role. Must be 'admin' or 'tech'"
        
        self.users[username] = {
            "password_hash": self.hash_password(password),
            "role": role,
            "active": True,
            "created_date": time.strftime("%Y-%m-%d")
        }
        
        if self.save_user_config():
            return True, "User created successfully"
        else:
            return False, "Failed to save user configuration"
    
    def delete_user(self, username):
        """
        Delete a user (only admins can do this)
        """
        if self.current_user_role != "admin":
            return False, "Only administrators can delete users"
        
        if username == self.current_user:
            return False, "Cannot delete currently logged in user"
        
        if username not in self.users:
            return False, "User does not exist"
        
        # Don't allow deletion of the last admin
        admin_count = sum(1 for user in self.users.values() if user["role"] == "admin" and user.get("active", True))
        if self.users[username]["role"] == "admin" and admin_count <= 1:
            return False, "Cannot delete the last administrator"
        
        del self.users[username]
        
        if self.save_user_config():
            return True, "User deleted successfully"
        else:
            return False, "Failed to save user configuration"
    
    def update_user_password(self, username, new_password):
        """
        Update a user's password
        """
        if username not in self.users:
            return False, "User does not exist"
        
        # Only admins can change other users' passwords, users can change their own
        if username != self.current_user and self.current_user_role != "admin":
            return False, "Insufficient permissions"
        
        self.users[username]["password_hash"] = self.hash_password(new_password)
        
        if self.save_user_config():
            self.log_activity("Password Updated", f"Password updated for user: {username}")
            return True, "Password updated successfully"
        else:
            return False, "Failed to save user configuration"
    
    def load_activity_log(self):
        """Load activity log from file"""
        log_file = 'activity_log.json'
        try:
            if os.path.exists(log_file):
                with open(log_file, 'r') as f:
                    self.activity_log = json.load(f)
            else:
                self.activity_log = []
        except Exception as e:
            print(f"Error loading activity log: {e}")
            self.activity_log = []
    
    def save_activity_log(self):
        """Save activity log to file"""
        log_file = 'activity_log.json'
        try:
            with open(log_file, 'w') as f:
                json.dump(self.activity_log, f, indent=4)
            return True
        except Exception as e:
            print(f"Error saving activity log: {e}")
            return False
    
    def log_activity(self, action, details):
        """Log an activity with timestamp and user info"""
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        log_entry = {
            "timestamp": timestamp,
            "user": self.current_user or "Unknown",
            "role": self.current_user_role or "Unknown", 
            "action": action,
            "details": details
        }
        self.activity_log.append(log_entry)
        self.save_activity_log()
    
    def load_password_config(self):
        """
        Load password configuration from config.json file
        If file doesn't exist, create it with default passwords
        """
        config_file = 'config.json'
        
        # Default configuration with hashed passwords
        default_config = {
            "maintenance_password": self.hash_password("LBRT123!"),  # Default hashed password
            "ip_setup_password": self.hash_password("LBRT123!")     # Default hashed password
        }
        
        try:
            if os.path.exists(config_file):
                with open(config_file, 'r') as f:
                    config = json.load(f)
                    
                # Ensure all required keys are present
                if all(key in config for key in default_config.keys()):
                    self.maintenance_password = config["maintenance_password"]
                    self.ip_setup_password = config["ip_setup_password"]
                else:
                    # Missing keys, use defaults for missing ones
                    for key in default_config.keys():
                        if key not in config:
                            config[key] = default_config[key]
                    
                    # Save the updated config
                    with open(config_file, 'w') as f:
                        json.dump(config, f, indent=4)
                        
                    self.maintenance_password = config["maintenance_password"]
                    self.ip_setup_password = config["ip_setup_password"]
            else:
                # Create the file with default values
                with open(config_file, 'w') as f:
                    json.dump(default_config, f, indent=4)
                    
                self.maintenance_password = default_config["maintenance_password"]
                self.ip_setup_password = default_config["ip_setup_password"]
                
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load password configuration: {e}")
            # Fallback to default hashed passwords
            self.maintenance_password = default_config["maintenance_password"]
            self.ip_setup_password = default_config["ip_setup_password"]
    
    def save_password_config(self):
        """
        Legacy method for backward compatibility - now uses save_user_config
        """
        return self.save_user_config()

    def create_user_management_login_page(self):
        """Create login page for user management access"""
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True)

        # Header
        header_label = tk.Label(
            self.current_frame,
            text="User Management Access",
            font=("Segoe UI", 22, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.grid(row=0, column=0, columnspan=2, pady=30)

        # Username field
        username_label = tk.Label(
            self.current_frame,
            text="Username:",
            font=("Segoe UI", 14),
            bg='#1e1e1e',
            fg='white'
        )
        username_label.grid(row=1, column=0, columnspan=2, pady=10)

        self.username_entry = tk.Entry(
            self.current_frame,
            font=("Segoe UI", 14),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            justify='center',
            width=20
        )
        self.username_entry.grid(row=2, column=0, columnspan=2, pady=10, ipady=5)

        # Password field
        password_label = tk.Label(
            self.current_frame,
            text="Password:",
            font=("Segoe UI", 14),
            bg='#1e1e1e',
            fg='white'
        )
        password_label.grid(row=3, column=0, columnspan=2, pady=10)

        self.user_mgmt_password_entry = tk.Entry(
            self.current_frame,
            font=("Segoe UI", 14),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            justify='center',
            width=20,
            show='*'
        )
        self.user_mgmt_password_entry.grid(row=4, column=0, columnspan=2, pady=10, ipady=5)
        self.user_mgmt_password_entry.bind('<Return>', lambda e: self.validate_user_management_login())

        # Buttons
        button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        button_frame.grid(row=5, column=0, columnspan=2, pady=30)

        login_button = HoverButton(
            button_frame,
            text="Login",
            command=self.validate_user_management_login,
            font=("Segoe UI", 14),
            bg="#107c10",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#25902a"
        )
        login_button.pack(side='left', padx=10, ipady=5)

        cancel_button = HoverButton(
            button_frame,
            text="Cancel",
            command=self.create_maintenance_page,
            font=("Segoe UI", 14),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#e85b24"
        )
        cancel_button.pack(side='left', padx=10, ipady=5)

    def validate_user_management_login(self):
        """Validate user login for user management access"""
        username = self.username_entry.get()
        password = self.user_mgmt_password_entry.get()
        
        role = self.authenticate_user(username, password)
        if role:
            self.create_user_management_page()
        else:
            messagebox.showerror("Access Denied", "Invalid username or password")
            self.username_entry.delete(0, tk.END)
            self.user_mgmt_password_entry.delete(0, tk.END)

    def create_user_management_page(self):
        """Create the main user management page"""
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True, fill='both', padx=20, pady=20)

        # Header with current user info
        header_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        header_frame.grid(row=0, column=0, columnspan=3, sticky='ew', pady=(0, 20))

        header_label = tk.Label(
            header_frame,
            text="User Management",
            font=("Segoe UI", 22, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.pack(side='left')

        user_info_label = tk.Label(
            header_frame,
            text=f"Logged in as: {self.current_user} ({self.current_user_role.title()})",
            font=("Segoe UI", 12),
            bg='#1e1e1e',
            fg='#00ff00'
        )
        user_info_label.pack(side='right')

        # User list section
        list_frame = tk.LabelFrame(
            self.current_frame,
            text="Current Users",
            font=("Segoe UI", 14, "bold"),
            bg='#1e1e1e',
            fg='white',
            bd=2,
            relief='groove'
        )
        list_frame.grid(row=1, column=0, columnspan=3, sticky='ew', pady=(0, 20), padx=10)

        # Create user list with scrollbar
        list_container = tk.Frame(list_frame, bg='#1e1e1e')
        list_container.pack(fill='both', expand=True, padx=10, pady=10)

        # Headers
        headers = ["Username", "Role", "Created", "Status", "Actions"]
        for i, header in enumerate(headers):
            tk.Label(
                list_container,
                text=header,
                font=("Segoe UI", 12, "bold"),
                bg='#1e1e1e',
                fg='white',
                width=12
            ).grid(row=0, column=i, padx=5, pady=5, sticky='w')

        # User rows
        row = 1
        for username, user_data in self.users.items():
            # Username
            tk.Label(
                list_container,
                text=username,
                font=("Segoe UI", 10),
                bg='#1e1e1e',
                fg='white',
                width=12
            ).grid(row=row, column=0, padx=5, pady=2, sticky='w')

            # Role
            role_color = '#00ff00' if user_data['role'] == 'admin' else '#ffff00'
            tk.Label(
                list_container,
                text=user_data['role'].title(),
                font=("Segoe UI", 10),
                bg='#1e1e1e',
                fg=role_color,
                width=12
            ).grid(row=row, column=1, padx=5, pady=2, sticky='w')

            # Created date
            tk.Label(
                list_container,
                text=user_data.get('created_date', 'Unknown'),
                font=("Segoe UI", 10),
                bg='#1e1e1e',
                fg='white',
                width=12
            ).grid(row=row, column=2, padx=5, pady=2, sticky='w')

            # Status
            status = "Active" if user_data.get('active', True) else "Inactive"
            status_color = '#00ff00' if user_data.get('active', True) else '#ff0000'
            tk.Label(
                list_container,
                text=status,
                font=("Segoe UI", 10),
                bg='#1e1e1e',
                fg=status_color,
                width=12
            ).grid(row=row, column=3, padx=5, pady=2, sticky='w')

            # Actions
            action_frame = tk.Frame(list_container, bg='#1e1e1e')
            action_frame.grid(row=row, column=4, padx=5, pady=2, sticky='w')

            if self.current_user_role == 'admin' and username != self.current_user:
                delete_btn = HoverButton(
                    action_frame,
                    text="Delete",
                    command=lambda u=username: self.confirm_delete_user(u),
                    font=("Segoe UI", 8),
                    bg="#d83b01",
                    fg="white",
                    relief="flat",
                    padx=5,
                    hover_color="#e85b24"
                )
                delete_btn.pack(side='left', padx=2)

            row += 1

        # User creation section (only for admins)
        if self.current_user_role == 'admin':
            create_frame = tk.LabelFrame(
                self.current_frame,
                text="Create New User",
                font=("Segoe UI", 14, "bold"),
                bg='#1e1e1e',
                fg='white',
                bd=2,
                relief='groove'
            )
            create_frame.grid(row=2, column=0, columnspan=3, sticky='ew', pady=(0, 20), padx=10)

            create_container = tk.Frame(create_frame, bg='#1e1e1e')
            create_container.pack(fill='x', padx=10, pady=10)

            # Username field
            tk.Label(
                create_container,
                text="Username:",
                font=("Segoe UI", 12),
                bg='#1e1e1e',
                fg='white'
            ).grid(row=0, column=0, padx=5, pady=5, sticky='e')

            self.new_username_entry = tk.Entry(
                create_container,
                font=("Segoe UI", 12),
                bg='#2d2d2d',
                fg='white',
                insertbackground='white',
                relief='flat',
                width=15
            )
            self.new_username_entry.grid(row=0, column=1, padx=5, pady=5, sticky='w')

            # Password field
            tk.Label(
                create_container,
                text="Password:",
                font=("Segoe UI", 12),
                bg='#1e1e1e',
                fg='white'
            ).grid(row=0, column=2, padx=5, pady=5, sticky='e')

            self.new_password_entry = tk.Entry(
                create_container,
                font=("Segoe UI", 12),
                bg='#2d2d2d',
                fg='white',
                insertbackground='white',
                relief='flat',
                show='*',
                width=15
            )
            self.new_password_entry.grid(row=0, column=3, padx=5, pady=5, sticky='w')

            # Role selection
            tk.Label(
                create_container,
                text="Role:",
                font=("Segoe UI", 12),
                bg='#1e1e1e',
                fg='white'
            ).grid(row=1, column=0, padx=5, pady=5, sticky='e')

            self.role_var = tk.StringVar(value="tech")
            role_frame = tk.Frame(create_container, bg='#1e1e1e')
            role_frame.grid(row=1, column=1, padx=5, pady=5, sticky='w')

            tk.Radiobutton(
                role_frame,
                text="Tech",
                variable=self.role_var,
                value="tech",
                font=("Segoe UI", 10),
                bg='#1e1e1e',
                fg='white',
                selectcolor='#2d2d2d',
                activebackground='#1e1e1e',
                activeforeground='white'
            ).pack(side='left')

            tk.Radiobutton(
                role_frame,
                text="Admin",
                variable=self.role_var,
                value="admin",
                font=("Segoe UI", 10),
                bg='#1e1e1e',
                fg='white',
                selectcolor='#2d2d2d',
                activebackground='#1e1e1e',
                activeforeground='white'
            ).pack(side='left', padx=(10, 0))

            # Create button
            create_user_btn = HoverButton(
                create_container,
                text="Create User",
                command=self.create_new_user,
                font=("Segoe UI", 12),
                bg="#107c10",
                fg="white",
                relief="flat",
                padx=15,
                hover_color="#25902a"
            )
            create_user_btn.grid(row=1, column=2, columnspan=2, padx=5, pady=5)

        # Master Maintenance Mode section (only for admins)
        if self.current_user_role == 'admin':
            master_frame = tk.LabelFrame(
                self.current_frame,
                text="Master Maintenance Mode",
                font=("Segoe UI", 14, "bold"),
                bg='#1e1e1e',
                fg='white',
                bd=2,
                relief='groove'
            )
            master_frame.grid(row=3, column=0, columnspan=3, sticky='ew', pady=(20, 20), padx=10)

            master_container = tk.Frame(master_frame, bg='#1e1e1e')
            master_container.pack(fill='x', padx=10, pady=10)

            # Initialize master maintenance mode variable if not exists
            if not hasattr(self, 'master_maintenance_mode'):
                self.master_maintenance_mode = False

            self.master_maintenance_var = tk.BooleanVar(value=self.master_maintenance_mode)
            
            master_checkbox = tk.Checkbutton(
                master_container,
                text="Enable Master Maintenance Mode (Activates SP Controls globally)",
                variable=self.master_maintenance_var,
                command=self.toggle_master_maintenance_mode,
                font=("Segoe UI", 12),
                bg='#1e1e1e',
                fg='white',
                selectcolor='#2d2d2d',
                activebackground='#1e1e1e',
                activeforeground='white'
            )
            master_checkbox.pack(anchor='w', pady=5)

            # Status label
            status_text = "ACTIVE" if self.master_maintenance_mode else "INACTIVE"
            status_color = '#00ff00' if self.master_maintenance_mode else '#ff0000'
            
            tk.Label(
                master_container,
                text=f"Status: {status_text}",
                font=("Segoe UI", 11, "bold"),
                bg='#1e1e1e',
                fg=status_color
            ).pack(anchor='w', pady=(0, 5))

        # Navigation buttons
        nav_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        nav_frame.grid(row=4, column=0, columnspan=3, pady=20)

        back_button = HoverButton(
            nav_frame,
            text="Back to Maintenance",
            command=self.create_maintenance_page,
            font=("Segoe UI", 14),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#2b88d8"
        )
        back_button.pack(side='left', padx=10, ipady=5)

        logout_button = HoverButton(
            nav_frame,
            text="Logout",
            command=self.logout_user,
            font=("Segoe UI", 14),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#e85b24"
        )
        logout_button.pack(side='left', padx=10, ipady=5)

    def toggle_master_maintenance_mode(self):
        """Toggle master maintenance mode - activates SP controls globally"""
        self.master_maintenance_mode = self.master_maintenance_var.get()
        
        # Update the global maintenance_mode_active based on master mode
        self.maintenance_mode_active = self.master_maintenance_mode
        
        # Save the state to config file for persistence
        self.save_user_config()
        
        # Log the activity
        status = "activated" if self.master_maintenance_mode else "deactivated"
        self.log_activity("Master Maintenance Mode", f"Master maintenance mode {status} by {self.current_user}")
        
        # Show confirmation message
        if self.master_maintenance_mode:
            messagebox.showinfo("Master Maintenance Mode", 
                              "Master Maintenance Mode ACTIVATED!\nSP Controls are now globally enabled.\nState saved to memory.")
        else:
            messagebox.showinfo("Master Maintenance Mode", 
                              "Master Maintenance Mode DEACTIVATED!\nSP Controls are now globally disabled.\nState saved to memory.")
        
        # Refresh the user management page to update status display
        self.create_user_management_page()

        # Activity Log button (only for admins)
        if self.current_user_role == 'admin':
            log_button = HoverButton(
                nav_frame,
                text="View Activity Log",
                command=self.create_activity_log_page,
                font=("Segoe UI", 14),
                bg="#ff8c00",
                fg="white",
                relief="flat",
                padx=30,
                hover_color="#ffa500"
            )
            log_button.pack(side='left', padx=10, ipady=5)

    def create_new_user(self):
        """Create a new user from the form"""
        username = self.new_username_entry.get().strip()
        password = self.new_password_entry.get()
        role = self.role_var.get()

        if not username or not password:
            messagebox.showerror("Error", "Username and password are required")
            return

        if len(username) < 3:
            messagebox.showerror("Error", "Username must be at least 3 characters long")
            return

        if len(password) < 6:
            messagebox.showerror("Error", "Password must be at least 6 characters long")
            return

        success, message = self.create_user(username, password, role)
        if success:
            self.log_activity("User Created", f"Created new user: {username} with role: {role}")
            messagebox.showinfo("Success", message)
            self.new_username_entry.delete(0, tk.END)
            self.new_password_entry.delete(0, tk.END)
            self.role_var.set("tech")
            self.create_user_management_page()  # Refresh the page
        else:
            messagebox.showerror("Error", message)

    def confirm_delete_user(self, username):
        """Confirm user deletion"""
        if messagebox.askyesno("Confirm Delete", f"Are you sure you want to delete user '{username}'?"):
            success, message = self.delete_user(username)
            if success:
                self.log_activity("User Deleted", f"Deleted user: {username}")
                messagebox.showinfo("Success", message)
                self.create_user_management_page()  # Refresh the page
            else:
                messagebox.showerror("Error", message)

    def logout_user(self):
        """Logout current user"""
        self.current_user = None
        self.current_user_role = None
        self.create_maintenance_page()

    def create_activity_log_page(self):
        """Create the activity log viewing page (admin only)"""
        if self.current_user_role != 'admin':
            messagebox.showerror("Access Denied", "Only administrators can view the activity log")
            return

        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True, fill='both', padx=20, pady=20)

        # Header
        header_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        header_frame.grid(row=0, column=0, columnspan=2, sticky='ew', pady=(0, 20))

        header_label = tk.Label(
            header_frame,
            text="Activity Log",
            font=("Segoe UI", 22, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.pack(side='left')

        user_info_label = tk.Label(
            header_frame,
            text=f"Logged in as: {self.current_user} ({self.current_user_role.title()})",
            font=("Segoe UI", 12),
            bg='#1e1e1e',
            fg='#00ff00'
        )
        user_info_label.pack(side='right')

        # Log display frame with scrollbar
        log_frame = tk.LabelFrame(
            self.current_frame,
            text="Recent Activity",
            font=("Segoe UI", 14, "bold"),
            bg='#1e1e1e',
            fg='white',
            bd=2,
            relief='groove'
        )
        log_frame.grid(row=1, column=0, columnspan=2, sticky='nsew', pady=(0, 20))

        # Configure grid weights for resizing
        self.current_frame.grid_rowconfigure(1, weight=1)
        self.current_frame.grid_columnconfigure(0, weight=1)

        # Create scrollable text widget
        log_container = tk.Frame(log_frame, bg='#1e1e1e')
        log_container.pack(fill='both', expand=True, padx=10, pady=10)

        # Scrollbar
        scrollbar = tk.Scrollbar(log_container, bg='#2d2d2d', troughcolor='#1e1e1e')
        scrollbar.pack(side='right', fill='y')

        # Text widget for log display
        log_text = tk.Text(
            log_container,
            font=("Consolas", 10),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            wrap='word',
            yscrollcommand=scrollbar.set,
            state='disabled'
        )
        log_text.pack(side='left', fill='both', expand=True)
        scrollbar.config(command=log_text.yview)

        # Populate log entries
        log_text.config(state='normal')
        log_text.delete(1.0, tk.END)

        if not self.activity_log:
            log_text.insert(tk.END, "No activity logged yet.\n")
        else:
            # Sort log entries by timestamp (newest first)
            sorted_log = sorted(self.activity_log, key=lambda x: x['timestamp'], reverse=True)
            
            for entry in sorted_log:
                timestamp = entry.get('timestamp', 'Unknown')
                user = entry.get('user', 'Unknown')
                role = entry.get('role', 'Unknown')
                action = entry.get('action', 'Unknown')
                details = entry.get('details', 'No details')
                
                # Format log entry
                log_entry = f"[{timestamp}] {user} ({role}) - {action}\n"
                log_entry += f"  Details: {details}\n"
                log_entry += "-" * 80 + "\n\n"
                
                log_text.insert(tk.END, log_entry)

        log_text.config(state='disabled')

        # Filter options
        filter_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        filter_frame.grid(row=2, column=0, columnspan=2, pady=(0, 20))

        tk.Label(
            filter_frame,
            text="Filter by Action:",
            font=("Segoe UI", 12),
            bg='#1e1e1e',
            fg='white'
        ).pack(side='left', padx=5)

        self.filter_var = tk.StringVar(value="All")
        filter_options = ["All", "Login", "SP Controls", "Turbo Threshold Changed", "User Created", "User Deleted", "Password Updated", "IP Configuration"]
        
        filter_combo = ttk.Combobox(
            filter_frame,
            textvariable=self.filter_var,
            values=filter_options,
            state="readonly",
            width=20
        )
        filter_combo.pack(side='left', padx=5)
        filter_combo.bind('<<ComboboxSelected>>', lambda e: self.filter_activity_log(log_text))

        refresh_button = HoverButton(
            filter_frame,
            text="Refresh",
            command=lambda: self.refresh_activity_log(log_text),
            font=("Segoe UI", 10),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=10,
            hover_color="#2b88d8"
        )
        refresh_button.pack(side='left', padx=10)

        # Navigation buttons
        nav_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        nav_frame.grid(row=3, column=0, columnspan=2, pady=20)

        back_button = HoverButton(
            nav_frame,
            text="Back to User Management",
            command=self.create_user_management_page,
            font=("Segoe UI", 14),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#2b88d8"
        )
        back_button.pack(side='left', padx=10, ipady=5)

        clear_log_button = HoverButton(
            nav_frame,
            text="Clear Log",
            command=self.clear_activity_log,
            font=("Segoe UI", 14),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#e85b24"
        )
        clear_log_button.pack(side='left', padx=10, ipady=5)

    def filter_activity_log(self, log_text):
        """Filter activity log by selected action"""
        filter_value = self.filter_var.get()
        
        log_text.config(state='normal')
        log_text.delete(1.0, tk.END)

        if not self.activity_log:
            log_text.insert(tk.END, "No activity logged yet.\n")
        else:
            # Filter and sort log entries
            if filter_value == "All":
                filtered_log = self.activity_log
            else:
                filtered_log = [entry for entry in self.activity_log if entry.get('action', '') == filter_value]
            
            sorted_log = sorted(filtered_log, key=lambda x: x['timestamp'], reverse=True)
            
            if not sorted_log:
                log_text.insert(tk.END, f"No activities found for filter: {filter_value}\n")
            else:
                for entry in sorted_log:
                    timestamp = entry.get('timestamp', 'Unknown')
                    user = entry.get('user', 'Unknown')
                    role = entry.get('role', 'Unknown')
                    action = entry.get('action', 'Unknown')
                    details = entry.get('details', 'No details')
                    
                    log_entry = f"[{timestamp}] {user} ({role}) - {action}\n"
                    log_entry += f"  Details: {details}\n"
                    log_entry += "-" * 80 + "\n\n"
                    
                    log_text.insert(tk.END, log_entry)

        log_text.config(state='disabled')

    def refresh_activity_log(self, log_text):
        """Refresh the activity log display"""
        self.load_activity_log()
        self.filter_activity_log(log_text)

    def clear_activity_log(self):
        """Clear the activity log (admin only)"""
        if self.current_user_role != 'admin':
            messagebox.showerror("Access Denied", "Only administrators can clear the activity log")
            return
        
        if messagebox.askyesno("Confirm Clear", "Are you sure you want to clear the entire activity log? This action cannot be undone."):
            self.activity_log = []
            self.save_activity_log()
            self.log_activity("Log Cleared", "Activity log cleared by administrator")
            messagebox.showinfo("Success", "Activity log has been cleared")
            self.create_activity_log_page()  # Refresh the page

    def create_password_page(self):
        # Deactivate auto fan when navigating to maintenance
        if self.auto_control_active:
            print("Deactivating auto fan control due to maintenance navigation")
            self.auto_control_active = False
            
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True)

        # Header
        header_label = tk.Label(
            self.current_frame,
            text="Maintenance Access",
            font=("Segoe UI", 22, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.grid(row=0, column=0, columnspan=2, pady=30)

        # Username field
        username_label = tk.Label(
            self.current_frame,
            text="Username:",
            font=("Segoe UI", 14),
            bg='#1e1e1e',
            fg='white'
        )
        username_label.grid(row=1, column=0, columnspan=2, pady=10)

        self.maint_username_entry = tk.Entry(
            self.current_frame,
            font=("Segoe UI", 14),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            justify='center',
            width=20
        )
        self.maint_username_entry.grid(row=2, column=0, columnspan=2, pady=10, ipady=5)

        # Password field
        password_label = tk.Label(
            self.current_frame,
            text="Password:",
            font=("Segoe UI", 14),
            bg='#1e1e1e',
            fg='white'
        )
        password_label.grid(row=3, column=0, columnspan=2, pady=10)

        self.password_entry = tk.Entry(
            self.current_frame,
            font=("Segoe UI", 14),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            justify='center',
            width=20,
            show='*'  # Hide password characters
        )
        self.password_entry.grid(row=4, column=0, columnspan=2, pady=10, ipady=5)
        self.password_entry.bind('<Return>', lambda e: self.validate_password())

        # Buttons
        button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        button_frame.grid(row=5, column=0, columnspan=2, pady=30)

        login_button = HoverButton(
            button_frame,
            text="Login",
            command=self.validate_password,
            font=("Segoe UI", 14),
            bg="#107c10",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#25902a"
        )
        login_button.pack(side='left', padx=10, ipady=5)

        cancel_button = HoverButton(
            button_frame,
            text="Cancel",
            command=self.create_monitor_page,
            font=("Segoe UI", 14),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#e85b24"
        )
        cancel_button.pack(side='left', padx=10, ipady=5)

    def validate_password(self):
        username = self.maint_username_entry.get()
        password = self.password_entry.get()
        
        role = self.authenticate_user(username, password)
        if role:
            self.log_activity("Login", f"User logged into maintenance page")
            self.create_maintenance_page()
        else:
            messagebox.showerror("Access Denied", "Invalid username or password")
            self.maint_username_entry.delete(0, tk.END)
            self.password_entry.delete(0, tk.END)

    def create_ip_setup_password_page(self):
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True)

        # Header
        header_label = tk.Label(
            self.current_frame,
            text="IP Setup Access",
            font=("Segoe UI", 22, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.grid(row=0, column=0, columnspan=2, pady=30)

        # Username field
        username_label = tk.Label(
            self.current_frame,
            text="Username:",
            font=("Segoe UI", 14),
            bg='#1e1e1e',
            fg='white'
        )
        username_label.grid(row=1, column=0, columnspan=2, pady=10)

        self.ip_username_entry = tk.Entry(
            self.current_frame,
            font=("Segoe UI", 14),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            justify='center',
            width=20
        )
        self.ip_username_entry.grid(row=2, column=0, columnspan=2, pady=10, ipady=5)

        # Password field
        password_label = tk.Label(
            self.current_frame,
            text="Password:",
            font=("Segoe UI", 14),
            bg='#1e1e1e',
            fg='white'
        )
        password_label.grid(row=3, column=0, columnspan=2, pady=10)

        self.ip_setup_password_entry = tk.Entry(
            self.current_frame,
            font=("Segoe UI", 14),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            justify='center',
            width=20,
            show='*'
        )
        self.ip_setup_password_entry.grid(row=4, column=0, columnspan=2, pady=10, ipady=5)
        self.ip_setup_password_entry.bind('<Return>', lambda e: self.validate_ip_setup_password())

        # Buttons
        button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        button_frame.grid(row=5, column=0, columnspan=2, pady=30)

        login_button = HoverButton(
            button_frame,
            text="Login",
            command=self.validate_ip_setup_password,
            font=("Segoe UI", 14),
            bg="#107c10",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#25902a"
        )
        login_button.pack(side='left', padx=10, ipady=5)

        cancel_button = HoverButton(
            button_frame,
            text="Cancel",
            command=self.create_ini_page2,
            font=("Segoe UI", 14),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#e85b24"
        )
        cancel_button.pack(side='left', padx=10, ipady=5)

    def validate_ip_setup_password(self):
        username = self.ip_username_entry.get()
        password = self.ip_setup_password_entry.get()
        
        role = self.authenticate_user(username, password)
        if role:
            self.log_activity("Login", f"User logged into IP setup page")
            self.create_ip_setup_page()
        else:
            messagebox.showerror("Access Denied", "Invalid username or password")
            self.ip_username_entry.delete(0, tk.END)
            self.ip_setup_password_entry.delete(0, tk.END)

        cancel_button = HoverButton(
            button_frame,
            text="Cancel",
            command=self.create_ini_page2,
            font=("Segoe UI", 14),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#e85b24"
        )
        cancel_button.pack(side='left', padx=10, ipady=5)

    def create_maintenance_page(self):
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True)

        # Header with user info
        header_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        header_frame.grid(row=0, column=0, columnspan=3, sticky='ew', pady=(0, 20))

        header_label = tk.Label(
            header_frame,
            text="Maintenance Page",
            font=("Segoe UI", 22, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.pack(side='left')

        if self.current_user:
            user_info_label = tk.Label(
                header_frame,
                text=f"Logged in as: {self.current_user} ({self.current_user_role.title()})",
                font=("Segoe UI", 12),
                bg='#1e1e1e',
                fg='#00ff00'
            )
            user_info_label.pack(side='right')

        # SP Controls section
        sp_controls_label = tk.Label(
            self.current_frame,
            text="SP Controls",
            font=("Segoe UI", 16, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        sp_controls_label.grid(row=1, column=0, columnspan=3, pady=(20, 10))

        # SP Control buttons
        button_frame1 = tk.Frame(self.current_frame, bg='#1e1e1e')
        button_frame1.grid(row=2, column=0, columnspan=3, pady=10)

        activate_button = HoverButton(
            button_frame1,
            text="Activate SP Controls",
            command=self.activate_maintenance_mode,
            font=("Segoe UI", 12),
            bg="#107c10",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#25902a"
        )
        activate_button.pack(side='left', padx=10, ipady=5)

        deactivate_button = HoverButton(
            button_frame1,
            text="Deactivate SP Controls", 
            command=self.deactivate_maintenance_mode,
            font=("Segoe UI", 12),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#e85b24"
        )
        deactivate_button.pack(side='left', padx=10, ipady=5)

        # Turbo Temperature Threshold section
        threshold_label = tk.Label(
            self.current_frame,
            text="Turbo Temperature Threshold",
            font=("Segoe UI", 16, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        threshold_label.grid(row=3, column=0, columnspan=3, pady=(40, 10))

        current_threshold_label = tk.Label(
            self.current_frame,
            text=f"Current Threshold: {self.turbo_temp_threshold}°F",
            font=("Segoe UI", 12),
            bg='#1e1e1e',
            fg='#00ff00'
        )
        current_threshold_label.grid(row=4, column=0, columnspan=3, pady=5)

        threshold_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        threshold_frame.grid(row=5, column=0, columnspan=3, pady=10)

        threshold_entry_label = tk.Label(
            threshold_frame,
            text="New Threshold (°F):",
            font=("Segoe UI", 12),
            bg='#1e1e1e',
            fg='white'
        )
        threshold_entry_label.pack(side='left', padx=5)

        self.threshold_entry = tk.Entry(
            threshold_frame,
            font=("Segoe UI", 12),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            width=10
        )
        self.threshold_entry.pack(side='left', padx=5)

        set_threshold_button = HoverButton(
            threshold_frame,
            text="Set Threshold",
            command=self.set_turbo_threshold,
            font=("Segoe UI", 12),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=15,
            hover_color="#2b88d8"
        )
        set_threshold_button.pack(side='left', padx=10)

        # Navigation buttons
        nav_button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        nav_button_frame.grid(row=6, column=0, columnspan=3, pady=40)

        back_button = HoverButton(
            nav_button_frame,
            text="Back to Monitor",
            command=self.create_monitor_page,
            font=("Segoe UI", 14),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#2b88d8"
        )
        back_button.pack(side='left', padx=10, ipady=5)
        
        # User Management button
        user_mgmt_button = HoverButton(
            nav_button_frame,
            text="User Management",
            command=self.create_user_management_login_page,
            font=("Segoe UI", 14),
            bg="#6f42c1",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#8a63d2"
        )
        user_mgmt_button.pack(side='left', padx=10, ipady=5)

    def set_turbo_threshold(self):
        try:
            new_threshold = int(self.threshold_entry.get())
            # Enforce safe numeric range of 950-1050°F
            if 950 <= new_threshold <= 1050:
                old_threshold = self.turbo_temp_threshold
                self.turbo_temp_threshold = new_threshold
                self.auto_threshold = new_threshold  # Update the auto threshold as well
                
                # Save the new threshold to config file for persistence
                self.save_user_config()
                
                self.log_activity("Turbo Threshold Changed", f"Changed from {old_threshold}°F to {new_threshold}°F")
                messagebox.showinfo("Success", f"Turbo temperature threshold set to {new_threshold}°F and saved to memory")
                self.create_maintenance_page()  # Refresh the page to show new value
            else:
                messagebox.showerror("Invalid Input", "Turbo temperature threshold must be between 950°F and 1050°F")
        except ValueError:
            messagebox.showerror("Invalid Input", "Please enter a valid number")

    def deactivate_maintenance_mode_from_monitor(self):
        self.maintenance_mode_active = False
        self.log_activity("SP Controls", "SP Controls deactivated from monitor page")
        messagebox.showinfo("Success", "SP Controls have been deactivated!")
        self.create_monitor_page()  # Refresh the monitor page to hide SP controls
        
    def activate_maintenance_mode(self):
        self.maintenance_mode_active = True
        self.log_activity("SP Controls", "SP Controls activated")
        messagebox.showinfo("Success", "SP Controls have been activated!")
        self.create_maintenance_page()  # Refresh the maintenance page
        
    def deactivate_maintenance_mode(self):
        self.maintenance_mode_active = False
        self.log_activity("SP Controls", "SP Controls deactivated")
        messagebox.showinfo("Success", "SP Controls have been deactivated!")
        self.create_maintenance_page()  # Refresh the maintenance page

    def create_maintenance_page(self):
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root, bg='#1e1e1e')
        self.current_frame.pack(expand=True)

        # Header
        header_label = tk.Label(
            self.current_frame,
            text="Maintenance Settings",
            font=("Segoe UI", 22, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.grid(row=0, column=0, columnspan=3, pady=20)

        # SP Controls Section
        sp_section_label = tk.Label(
            self.current_frame,
            text="Setpoint Controls",
            font=("Segoe UI", 16, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        sp_section_label.grid(row=1, column=0, columnspan=3, pady=(30, 10))

        # Current status
        status_text = "ACTIVE" if self.maintenance_mode_active else "INACTIVE"
        status_color = "#25902a" if self.maintenance_mode_active else "#d83b01"
        
        status_label = tk.Label(
            self.current_frame,
            text=f"SP Controls Status: {status_text}",
            font=("Segoe UI", 14),
            bg='#1e1e1e',
            fg=status_color
        )
        status_label.grid(row=2, column=0, columnspan=3, pady=10)

        # Activate/Deactivate buttons
        button_frame1 = tk.Frame(self.current_frame, bg='#1e1e1e')
        button_frame1.grid(row=3, column=0, columnspan=3, pady=20)

        activate_button = HoverButton(
            button_frame1,
            text="Activate SP Controls",
            command=self.activate_maintenance_mode,
            font=("Segoe UI", 12),
            bg="#107c10",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#25902a"
        )
        activate_button.pack(side='left', padx=10, ipady=5)

        deactivate_button = HoverButton(
            button_frame1,
            text="Deactivate SP Controls",
            command=self.deactivate_maintenance_mode,
            font=("Segoe UI", 12),
            bg="#d83b01",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#e85b24"
        )
        deactivate_button.pack(side='left', padx=10, ipady=5)

        # Turbo Temp Threshold Section
        threshold_section_label = tk.Label(
            self.current_frame,
            text="Turbo Temperature Threshold",
            font=("Segoe UI", 16, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        threshold_section_label.grid(row=4, column=0, columnspan=3, pady=(40, 10))

        # Current threshold display
        current_threshold_label = tk.Label(
            self.current_frame,
            text=f"Current Threshold: {self.turbo_temp_threshold}",
            font=("Segoe UI", 14),
            bg='#1e1e1e',
            fg='white'
        )
        current_threshold_label.grid(row=5, column=0, columnspan=3, pady=10)

        # Threshold input
        threshold_input_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        threshold_input_frame.grid(row=6, column=0, columnspan=3, pady=20)

        threshold_label = tk.Label(
            threshold_input_frame,
            text="New Threshold:",
            font=("Segoe UI", 12),
            bg='#1e1e1e',
            fg='white'
        )
        threshold_label.pack(side='left', padx=10)

        self.threshold_entry = tk.Entry(
            threshold_input_frame,
            font=("Segoe UI", 12),
            bg='#2d2d2d',
            fg='white',
            insertbackground='white',
            relief='flat',
            justify='center',
            width=10
        )
        self.threshold_entry.pack(side='left', padx=10, ipady=3)
        self.threshold_entry.insert(0, str(self.turbo_temp_threshold))

        set_threshold_button = HoverButton(
            threshold_input_frame,
            text="Set",
            command=self.set_turbo_threshold,
            font=("Segoe UI", 12),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=20,
            hover_color="#2b88d8"
        )
        set_threshold_button.pack(side='left', padx=10, ipady=3)

        # Navigation buttons
        nav_button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        nav_button_frame.grid(row=7, column=0, columnspan=3, pady=40)

        back_button = HoverButton(
            nav_button_frame,
            text="Turbo Monitor",
            command=self.create_monitor_page,
            font=("Segoe UI", 14),
            bg="#0078d4",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#2b88d8"
        )
        back_button.pack(side='left', padx=10, ipady=5)
        
        # User Management button
        user_mgmt_button = HoverButton(
            nav_button_frame,
            text="User Management",
            command=self.create_user_management_login_page,
            font=("Segoe UI", 14),
            bg="#6f42c1",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#8a63d2"
        )
        user_mgmt_button.pack(side='left', padx=10, ipady=5)
        
        # Controls button
        controls_button = HoverButton(
            nav_button_frame,
            text="Controls",
            command=self.create_controls_page,
            font=("Segoe UI", 14),
            bg="#ff6600",
            fg="white",
            relief="flat",
            padx=30,
            hover_color="#ff8533"
        )
        controls_button.pack(side='left', padx=10, ipady=5)

    # [Rest of the methods remain the same as in your provided code]
    def process_scan_results(self, string_result, int_result, ip):
        pump_number = ''
        for reg in string_result.registers:
            high_byte = (reg >> 8) & 0xFF
            low_byte = reg & 0xFF
            if high_byte != 0:
                pump_number += chr(high_byte)
            if low_byte != 0:
                pump_number += chr(low_byte)

        integer_value = int_result.registers[0]
        self.create_pump_files(pump_number, ip, integer_value)

    def create_pump_files(self, pump_number, ip, integer_value):
        new_folder = os.path.join(self.exe_folder, pump_number)
        os.makedirs(new_folder, exist_ok=True)

        if integer_value == 22:
            shutil.copy("PumperHMI 8.exe", os.path.join(new_folder, f"{pump_number}.exe"))
            self.write_ini_file(new_folder, ip, version=8)
        elif integer_value == 1:
            shutil.copy("PumperHMI.exe", os.path.join(new_folder, f"{pump_number}.exe"))
            self.write_ini_file(new_folder, ip, version=1)

    def write_ini_file(self, folder, ip, version):
        with open(os.path.join(folder, "PumperHMI.ini"), 'w') as ini_file:
            if version == 8:
                ini_file.write(f"[cRIO]\nIPAddress = \"{ip}\"\n"
                               f"Webservice Name = WebService\n"
                               f"Webservice Port = 8002\n\n"
                               f"[HMI]\nWindow State = Invalid\n")
            else:
                ini_file.write(f"[PumperHMI]\n"
                               f"server.app.propertiesEnabled=True\n"
                               f"server.ole.enabled=True\n"
                               f"server.tcp.paranoid=True\n"
                               f'server.tcp.serviceName="My Computer/VI Server"\n'
                               f"server.vi.callsEnabled=True\n"
                               f"server.vi.propertiesEnabled=True\n"
                               f'WebServer.TcpAccess="c+*"\n'
                               f'WebServer.ViAccess="+*"\n'
                               f"DebugServerEnabled=False\n"
                               f"DebugServerWaitOnLaunch=False\n"
                               f"blinkFG=00FF0000\n\n"
                               f"[cRIO]\n"
                               f"IPAddress = \"{ip}\"\n"
                               f"Webservice Name = WebService\n"
                               f"Webservice Port = 8002\n\n"
                               f"[HMI]\n"
                               f'Window State="Standard"\n'
                               f"Resizable?=True\n"
                               f"TimeZone=-21600\n")

    def get_exe_files(self):
        exe_files = []
        if os.path.exists(self.exe_folder):
            for root, dirs, files in os.walk(self.exe_folder):
                for file in files:
                    if file.endswith('.exe'):
                        exe_files.append(os.path.join(root, file))
        return exe_files

    def save_assignments(self):
        try:
            assignments_data = {}
            for pump_index, data in self.pump_assignments.items():
                if isinstance(data, dict) and 'dropdown' in data:
                    assignments_data[str(pump_index)] = {
                        "exe_name": data['dropdown'].get()
                    }
            with open('pump_assignments.json', 'w') as f:
                json.dump(assignments_data, f)
        except Exception as e:
            print(f"Error saving assignments: {e}")

    def load_assignments(self):
        try:
            if os.path.exists('pump_assignments.json'):
                with open('pump_assignments.json', 'r') as f:
                    assignments = json.load(f)
                    # Convert string keys to integers
                    return {int(k): {"exe_name": v["exe_name"]} for k, v in assignments.items()}
        except Exception as e:
            print(f"Error loading assignments: {e}")
        return {}

    def set_pump_assignment(self, pump_index, dropdown):
        selected_exe = dropdown.get()
        if selected_exe != "Select Pump":
            exe_path = next((file for file in self.exe_files if os.path.basename(file)[:-4] == selected_exe), None)
            if exe_path:
                self.run_exe(exe_path)
                self.save_assignments()
        else:
            messagebox.showwarning("Invalid Selection", "Please select a pump before setting.")

    def run_exe(self, exe_path):
        def kill_processes():
            try:
                # Get list of running processes with their executable names
                process_list = subprocess.check_output(['tasklist', '/FO', 'CSV', '/NH'],
                                                       universal_newlines=True).split('\n')

                # Get basenames of all exe files except the target
                target_exe = os.path.basename(exe_path)
                exe_basenames = [os.path.basename(exe) for exe in self.exe_files if os.path.basename(exe) != target_exe]

                # Kill each running process that matches our exe files
                for process in process_list:
                    if process:  # Skip empty lines
                        try:
                            process_name = process.split(',')[0].strip('"')
                            if process_name in exe_basenames:
                                subprocess.run(['taskkill', '/F', '/IM', process_name],
                                               stdout=subprocess.DEVNULL,
                                               stderr=subprocess.DEVNULL)
                                time.sleep(0.1)  # Small delay to ensure process is killed
                        except Exception as e:
                            print(f"Error killing process {process_name}: {e}")

            except Exception as e:
                print(f"Error in kill_processes: {e}")

        try:
            # Kill existing processes first and wait for completion
            kill_thread = threading.Thread(target=kill_processes)
            kill_thread.start()
            kill_thread.join(timeout=1.0)  # Wait up to 3 seconds for processes to be killed

            # Start new process
            subprocess.Popen(exe_path)

        except Exception as e:
            print(f"Error starting process: {e}")


    def create_monitor_page(self):
        # Track current monitoring state before stopping
        self.was_monitoring_before_navigation = self.monitoring_active
        
        # Stop any existing monitor threads
        self.stop_monitoring()
        
        if self.current_frame:
            self.current_frame.destroy()

        # Set up the main frame
        self.current_frame = tk.Frame(self.root)
        self.current_frame.configure(bg='#1e1e1e')
        self.current_frame.pack(expand=True, fill='both', padx=30, pady=20)
        
        # Modern header with subtle bottom border
        header_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        header_frame.pack(fill='x', pady=(0, 5))
        
        header_label = tk.Label(
            header_frame,
            text="Prime Turbo Temp Monitor",
            font=("Segoe UI", 26, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.pack(pady=(0, 5))
        
        separator = ttk.Separator(header_frame, orient='horizontal')
        separator.pack(fill='x', padx=50)
        
        # Find 230xx and LFPC folders for turbo temp monitoring
        self.units_info = self.find_230xx_folders() + self.find_lfpc_folders()
        
        if not self.units_info:
            # Create a placeholder frame for consistent layout
            placeholder_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
            placeholder_frame.pack(expand=True, fill='both')
            
            no_units_label = tk.Label(
                placeholder_frame,
                text="No 230xx units found. Please scan for units first.",
                font=("Segoe UI", 16),
                bg='#1e1e1e',
                fg='white'
            )
            no_units_label.pack(expand=True, pady=50)
            
            # Modern styled bottom control buttons
            button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
            button_frame.pack(side='bottom', pady=25)
            
            # Back button
            back_button = HoverButton(
                button_frame,
                text="Back",
                width=15,
                font=("Segoe UI", 12, "bold"),
                bg="#0078d4",
                fg="white",
                relief="flat",
                hover_color="#2b88d8",  # Lighter blue on hover
                command=self.load_existing_configuration
            )
            back_button.pack(side='left', padx=10, ipady=5)
            return
        
        # Create a frame for the units display with modern styling
        self.grid_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        self.grid_frame.pack(expand=True, fill='both', padx=10, pady=10)
        
        # Create monitor displays for each unit
        self.create_unit_monitors()
        
        # Modern styled bottom control buttons
        button_frame = tk.Frame(self.current_frame, bg='#1e1e1e', pady=15)
        button_frame.pack(side='bottom', fill='x')
        
        # Auto control button - set initial state based on current auto_control_active
        if self.auto_control_active:
            button_text = "Auto Fan ON"
            button_bg = "#107c10"  # Green when active
            hover_color = "#25902a"  # Lighter green on hover
        else:
            button_text = "Auto Fan OFF"
            button_bg = "#0078d4"  # Blue when inactive
            hover_color = "#2b88d8"  # Lighter blue on hover
            
        self.auto_button = HoverButton(
            button_frame,
            text=button_text,
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg=button_bg,
            fg="white",
            relief="flat",
            hover_color=hover_color,
            command=self.toggle_auto_control
        )
        self.auto_button.pack(side='left', padx=10, ipady=5)
        
        # Start monitoring button
        self.start_button = HoverButton(
            button_frame,
            text="Start Monitoring",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#107c10",
            fg="white",
            relief="flat",
            hover_color="#25902a",  # Lighter green on hover
            command=self.start_monitoring
        )
        self.start_button.pack(side='left', padx=10, ipady=5)
        
        # Stop monitoring button
        self.stop_button = HoverButton(
            button_frame,
            text="Stop Monitoring",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#d83b01",
            fg="white",
            relief="flat",
            hover_color="#e85b24",  # Lighter red on hover
            command=self.stop_monitoring
        )
        self.stop_button.pack(side='left', padx=10, ipady=5)
        
        # Maintenance button
        maintenance_button = HoverButton(
            button_frame,
            text="Maintenance",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#6b69d6",
            fg="white",
            relief="flat",
            hover_color="#7b79e6",  # Lighter purple on hover
            command=self.create_password_page
        )
        maintenance_button.pack(side='left', padx=10, ipady=5)
        
        # Deactivate button (only visible when maintenance mode is active and master maintenance mode is NOT active)
        if self.maintenance_mode_active and not self.master_maintenance_mode:
            deactivate_button = HoverButton(
                button_frame,
                text="Deactivate SP",
                width=15,
                font=("Segoe UI", 12, "bold"),
                bg="#d83b01",
                fg="white",
                relief="flat",
                hover_color="#e85b24",  # Lighter red on hover
                command=self.deactivate_maintenance_mode_from_monitor
            )
            deactivate_button.pack(side='left', padx=10, ipady=5)
        
        # Operations button
        # operations_button = HoverButton(
        #     button_frame,
        #     text="Operations",
        #     width=15,
        #     font=("Segoe UI", 12, "bold"),
        #     bg="#ff8c00",
        #     fg="white",
        #     relief="flat",
        #     hover_color="#ffa500",
        #     command=self.create_operations_page
        # )
        # operations_button.pack(side='left', padx=10, ipady=5)
        
        # Back button
        back_button = HoverButton(
            button_frame,
            text="Back",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#0078d4",
            fg="white",
            relief="flat",
            hover_color="#2b88d8",  # Lighter blue on hover
            command=lambda: self.back_to_main()
        )
        back_button.pack(side='left', padx=10, ipady=5)
        
        # Auto-start monitoring if it was active before navigation
        if self.was_monitoring_before_navigation:
            self.root.after(100, self.start_monitoring)  # Delay to ensure UI is ready
        
    def find_230xx_folders(self):
        """Find all folders with names starting with '230' and read their IP addresses from .ini files"""
        units_info = []
        
        if os.path.exists(self.exe_folder):
            for folder in os.listdir(self.exe_folder):
                if folder.startswith('230'):
                    folder_path = os.path.join(self.exe_folder, folder)
                    
                    if os.path.isdir(folder_path):
                        # Try to read IP from .ini file
                        ip_address = self.read_ip_from_ini(folder_path)
                        if ip_address:
                            units_info.append({
                                'unit_name': folder,
                                'folder_path': folder_path,
                                'ip_address': ip_address
                            })
        
        return units_info
    
    def read_ip_from_ini(self, folder_path):
        """Read IP address from .ini file in the specified folder"""
        ini_path = os.path.join(folder_path, "PumperHMI.ini")
        if os.path.exists(ini_path):
            try:
                config = configparser.ConfigParser()
                config.read(ini_path)
                
                if 'cRIO' in config and 'IPAddress' in config['cRIO']:
                    # Extract IP address and remove quotes if present
                    ip = config['cRIO']['IPAddress'].strip('"')
                    return ip
                    
            except Exception as e:
                print(f"Error reading .ini file {ini_path}: {e}")
                
                # Try manual parsing if ConfigParser fails
                try:
                    with open(ini_path, 'r') as f:
                        content = f.read()
                        match = re.search(r'IPAddress\s*=\s*"([\d\.]+)"', content)
                        if match:
                            return match.group(1)
                except Exception as e:
                    print(f"Error in manual parsing of {ini_path}: {e}")
        
        return None
    
    def find_lfpc_folders(self):
        """Find all folders with names starting with 'LFPC' and read their IP addresses from .ini files"""
        lfpc_units_info = []
        
        if os.path.exists(self.exe_folder):
            for folder in os.listdir(self.exe_folder):
                if folder.startswith('LFPC'):
                    folder_path = os.path.join(self.exe_folder, folder)
                    
                    if os.path.isdir(folder_path):
                        # Try to read IP from .ini file
                        ip_address = self.read_ip_from_ini(folder_path)
                        if ip_address:
                            lfpc_units_info.append({
                                'unit_name': folder,
                                'folder_path': folder_path,
                                'ip_address': ip_address,
                                'unit_type': 'LFPC'
                            })
        
        return lfpc_units_info
    
    def create_unit_monitors(self):
        """Create monitoring displays for each unit"""
        # Load pump assignments to map pump numbers to unit numbers
        pump_assignments = self.load_assignments()
        
        # Create a mapping of unit numbers to their assigned pump numbers
        unit_to_pump_map = {}
        for pump_num, data in pump_assignments.items():
            if data.get('exe_name') != 'Select Pump':
                unit_to_pump_map[data.get('exe_name')] = pump_num
        
        # Sort units based on their pump assignments
        sorted_units = []
        unassigned_units = []
        
        for unit in self.units_info:
            unit_name = unit['unit_name']
            if unit_name in unit_to_pump_map.keys():
                # Add pump number to unit info
                unit['pump_number'] = unit_to_pump_map[unit_name]
                sorted_units.append(unit)
            else:
                # Unit not assigned to any pump
                unit['pump_number'] = None
                unassigned_units.append(unit)
        
        # Sort units by pump number
        sorted_units.sort(key=lambda u: int(u['pump_number']))
        
        # Add unassigned units at the end
        all_units = sorted_units + unassigned_units
        
        # Calculate rows and columns (5 rows per column)
        rows_per_column = 6
        num_units = len(all_units)
        num_columns = (num_units + rows_per_column - 1) // rows_per_column
        
        for i, unit in enumerate(all_units):
            # Calculate position (column first, then row)
            col = i // rows_per_column
            row = i % rows_per_column
            
            # Check if this is an LFPC unit
            is_lfpc = unit.get('unit_type') == 'LFPC'
            
            # Create a frame for this unit (50% smaller)
            unit_frame = tk.Frame(self.grid_frame, bg='#2d2d2d', padx=7, pady=7, bd=1, relief='solid', width=315, height=110, cursor='hand2')
            unit_frame.grid(row=row, column=col, padx=5, pady=5)  # Removed sticky to prevent size changes
            unit_frame.grid_propagate(False)  # Force the frame to maintain its size
            unit_frame.pack_propagate(False)  # Also prevent pack from changing size
            
            # Unit header with name and IP
            header = tk.Frame(unit_frame, bg='#2d2d2d')
            header.pack(fill='x')
            
            # Display format: "Pump # - Unit ###" if pump number exists
            # Add 1 to pump_number for display (so pump 0 shows as Pump 1)
            if unit['pump_number'] is not None:
                displayed_pump_num = int(unit['pump_number']) + 1
                label_text = f"Pump {displayed_pump_num} - Unit {unit['unit_name']}"
            else:
                label_text = f"Unit {unit['unit_name']}"
                
            unit_label = tk.Label(
                header,
                text=label_text,
                font=("Segoe UI", 10, "bold"),
                bg='#2d2d2d',
                fg='white'
            )
            unit_label.pack(side='left')
            
            ip_label = tk.Label(
                header,
                text=f"IP: {unit['ip_address']}",
                font=("Segoe UI", 8),
                bg='#2d2d2d',
                fg='#aaaaaa'
            )
            ip_label.pack(side='right')
            
            # Separator
            separator = ttk.Separator(unit_frame, orient='horizontal')
            separator.pack(fill='x', pady=5)
            
            # LFPC units: Display "Conventional" text in first row, controls in second row (matching Prime unit structure)
            if is_lfpc:
                # First row: "Conventional" text (matches Turbo row position)
                conventional_text_frame = tk.Frame(unit_frame, bg='#2d2d2d')
                conventional_text_frame.pack(fill='x', pady=2)
                
                conventional_label = tk.Label(
                    conventional_text_frame,
                    text="Conventional",
                    font=("Segoe UI", 10, "bold"),
                    bg='#2d2d2d',
                    fg='white'
                )
                conventional_label.pack(side='left', padx=5)
                
                # Second row: Status indicator and HMI button (matches Battery row position)
                controls_frame = tk.Frame(unit_frame, bg='#2d2d2d')
                controls_frame.pack(fill='x', pady=2)
                
                # Status label
                status_label = tk.Label(
                    controls_frame,
                    text="Status:",
                    font=("Segoe UI", 8),
                    bg='#2d2d2d',
                    fg='white'
                )
                status_label.pack(side='left', padx=5)
                
                # Status indicator light
                status_light = tk.Label(
                    controls_frame,
                    text="",
                    width=2,
                    height=1,
                    bg='gray',
                    relief='raised',
                    bd=1
                )
                status_light.pack(side='left', padx=2)
                
                # HMI button
                hmi_button = HoverButton(
                    controls_frame,
                    text="HMI",
                    width=4,
                    font=("Segoe UI", 9),
                    bg='#107c10',
                    fg='white',
                    relief="raised",
                    hover_color='green',
                    command=lambda u=unit: self.launch_unit_hmi(u)
                )
                hmi_button.pack(side='left', padx=3)
                
                # Store dummy values for LFPC units
                turbo_value = None
                battery_value = None
                setpoint_value = None
            else:
                # Prime (230xx) units: Display turbo and battery info
                # Status indicators frame (first row)
                indicators_frame = tk.Frame(unit_frame, bg='#2d2d2d')
                indicators_frame.pack(fill='x', pady=2)
                
                # Turbo Temp display - use sub-frame for stability
                turbo_frame = tk.Frame(indicators_frame, bg='#2d2d2d')
                turbo_frame.pack(side='left', padx=5)
                
                turbo_label = tk.Label(
                    turbo_frame,
                    text="Turbo:",
                    font=("Segoe UI", 8),
                    bg='#2d2d2d',
                    fg='white'
                )
                turbo_label.pack(side='left')
                
                turbo_value = tk.Label(
                    turbo_frame,
                    text="---",
                    font=("Segoe UI", 9, "bold"),
                    width=4,
                    bg='#1e1e1e',
                    fg='#00ff00',
                    relief='sunken',
                    bd=1,
                    anchor='e'  # Right-align to prevent shifting
                )
                turbo_value.pack(side='left', padx=5)
                
                # Status indicator - use sub-frame for stability
                status_frame = tk.Frame(indicators_frame, bg='#2d2d2d')
                status_frame.pack(side='left', padx=5)
                
                status_indicator = tk.Label(
                    status_frame,
                    text="Status:",
                    font=("Segoe UI", 8),
                    bg='#2d2d2d',
                    fg='white'
                )
                status_indicator.pack(side='left')
                
                status_light = tk.Label(
                    status_frame,
                    text="",
                    width=2,
                    height=1,
                    bg='gray',
                    relief='raised',
                    bd=1
                )
                status_light.pack(side='left', padx=5)
                
                # Button container frame for control and HMI buttons
                buttons_frame = tk.Frame(indicators_frame, bg='#2d2d2d')
                buttons_frame.pack(side='right', padx=5)
                
                # Control button for register 401000
                control_button = HoverButton(
                    buttons_frame,
                    text="Fan",
                    width=4,
                    font=("Segoe UI", 9),
                    bg='#0078d4',
                    fg='white',
                    relief="raised",
                    hover_color='#2b88d8',
                    command=lambda u=unit: self.toggle_control(u)
                )
                control_button.pack(side='left', padx=2)
                
                # HMI button to launch the unit's HMI interface
                hmi_button = HoverButton(
                    buttons_frame,
                    text="HMI",
                    width=4,
                    font=("Segoe UI", 9),
                    bg='#107c10',
                    fg='white',
                    relief="raised",
                    hover_color='green',
                    command=lambda u=unit: self.launch_unit_hmi(u)
                )
                hmi_button.pack(side='right', padx=2)
                
                # Battery % display - new row below Turbo Temp
                battery_frame = tk.Frame(unit_frame, bg='#2d2d2d')
                battery_frame.pack(fill='x', pady=2)
                
                battery_label = tk.Label(
                    battery_frame,
                    text="Batt%:",
                    font=("Segoe UI", 8),
                    bg='#2d2d2d',
                    fg='white'
                )
                battery_label.pack(side='left', padx=5)
                
                # Digital display for Battery %
                battery_value = tk.Label(
                    battery_frame,
                    text="---",
                    font=("Segoe UI", 9, "bold"),  # Match turbo font size
                    width=4,
                    bg='#1e1e1e',
                    fg='#00ff00',
                    relief='sunken',
                    bd=1,
                    anchor='e'  # Right-align to prevent shifting
                )
                battery_value.pack(side='left', padx=5)
            
            # SP Controls - visible when maintenance mode is active OR master maintenance mode is active (only for Prime units)
            if (self.maintenance_mode_active or self.master_maintenance_mode) and not is_lfpc:
                # Set Point display for register 401212
                setpoint_label = tk.Label(
                    battery_frame,
                    text="current SP:",
                    font=("Segoe UI", 8),
                    bg='#2d2d2d',
                    fg='white'
                )
                setpoint_label.pack(side='left', padx=5)
                
                # Digital display for Set Point
                setpoint_value = tk.Label(
                    battery_frame,
                    text="---",
                    font=("Segoe UI", 9, "bold"),
                    width=3,
                    bg='#1e1e1e',
                    fg='#00ff00',
                    relief='sunken',
                    bd=1,
                    anchor='e'  # Right-align to prevent shifting
                )
                setpoint_value.pack(side='left', padx=5)
                
                # Input box for register 401212
                value_label = tk.Label(
                    battery_frame,
                    text="SP:",
                    font=("Segoe UI", 8),
                    bg='#2d2d2d',
                    fg='white'
                )
                value_label.pack(side='left', padx=5)
                
                # Create a StringVar for the input value
                input_var = tk.StringVar()
                input_var.set("0")
                
                # Input entry for value (width=3 for up to 3 digits - max 100)
                value_entry = tk.Entry(
                    battery_frame,
                    textvariable=input_var,
                    font=("Segoe UI", 9),
                    width=3,
                    bg='#1e1e1e',
                    fg='white',
                    relief='sunken',
                    bd=1
                )
                value_entry.pack(side='left', padx=2)
                
                # Send button for the value
                send_button = HoverButton(
                    battery_frame,
                    text="Set",
                    width=4,
                    font=("Segoe UI", 9),
                    bg='red',
                    fg='white',
                    relief="raised",
                    hover_color='#4d0000',
                    command=lambda u=unit, v=input_var: self.send_register_value(u, v, 1212)
                )
                send_button.pack(side='left', padx=2)
            else:
                # Add setpoint_value as None when maintenance mode is inactive or LFPC
                setpoint_value = None
                input_var = None
                value_entry = None
            
            # Store widgets for both LFPC and Prime units
            if is_lfpc:
                unit['widgets'] = {
                    'unit_frame': unit_frame,
                    'hmi_button': hmi_button,
                    'turbo_value': None,
                    'battery_value': None,
                    'setpoint_value': None,
                    'status_light': status_light,
                    'control_button': None,
                    'input_var': None,
                    'value_entry': None,
                    'flash_state': False,
                    'bg_flash_state': False
                }
            else:
                # Prime units - all widgets already created above
                unit['widgets'] = {
                    'unit_frame': unit_frame,
                    'turbo_value': turbo_value,
                    'battery_value': battery_value,
                    'setpoint_value': setpoint_value,
                    'status_light': status_light,
                    'control_button': control_button,
                    'hmi_button': hmi_button,
                    'input_var': input_var,
                    'value_entry': value_entry,
                    'flash_state': False,
                    'bg_flash_state': False
                }
            
            # Bind click event to all widgets in the frame (for both LFPC and Prime)
            self.bind_click_recursive(unit_frame, lambda e, u=unit: self.open_unit_operations_window(u))
    
    def start_monitoring(self):
        """Start monitoring Modbus registers for all units"""
        if self.monitoring_active:
            return
            
        self.monitoring_active = True
        self.start_button.config(state='disabled')
        self.stop_button.config(state='normal')
        
        for unit in self.units_info:
            thread = threading.Thread(
                target=self.monitor_unit,
                args=(unit,),
                daemon=True
            )
            thread.start()
            self.monitor_threads.append(thread)
    
    def stop_monitoring(self):
        """Stop all monitoring threads"""
        if not self.monitoring_active:
            # Already stopped
            return
            
        # Set the flag to signal threads to exit their loops
        self.monitoring_active = False
        
        print("Stopping all monitoring threads...")
        
        # Only try to update buttons if they still exist in the widget hierarchy
        try:
            if hasattr(self, 'start_button') and self.start_button.winfo_exists():
                self.start_button.config(state='normal')
            if hasattr(self, 'stop_button') and self.stop_button.winfo_exists():
                self.stop_button.config(state='disabled')
        except (tk.TclError, RuntimeError, AttributeError):
            # Button was destroyed or doesn't exist anymore
            pass
        
        # Wait for threads to terminate with a reasonable timeout
        active_threads = []
        for thread in self.monitor_threads:
            if thread.is_alive():
                thread.join(1.5)  # Wait longer (1500ms) for each thread to terminate
                if thread.is_alive():
                    active_threads.append(thread)
        
        # Log any threads that didn't terminate in time
        if active_threads:
            print(f"Warning: {len(active_threads)} monitoring threads did not terminate properly")
                
        self.monitor_threads = []
    
    def monitor_unit(self, unit):
        """Monitor Modbus registers for a specific unit"""
        ip = unit['ip_address']
        unit_name = unit.get('unit_name', 'Unknown')
        is_lfpc = unit.get('unit_type') == 'LFPC'
        print(f"Starting monitoring thread for unit {unit_name} at {ip}")
        
        try:
            widgets = unit['widgets']
            flash_counter = 0
            unit_frame = widgets.get('unit_frame')
            
            while self.monitoring_active:
                # Exit if monitoring has been deactivated
                if not self.monitoring_active:
                    print(f"Monitoring deactivated for unit {unit_name}, exiting thread")
                    break
                
                client = ModbusTcpClient(ip)  # Create new client each iteration for better error handling
                
                try:
                    if client.connect():
                        if is_lfpc:
                            # LFPC unit monitoring - monitor PLC status only
                            # Read and update status indicator for LFPC units
                            # Check 300005.02 (bit 2 of register 5)
                            plc_result = client.read_input_registers(address=5, count=1)
                            plc_bit_set = False
                            
                            if not plc_result.isError():
                                plc_bit_set = bool(plc_result.registers[0] & 0x04)  # Check bit 2
                            
                            # Update the status indicator for LFPC
                            if widgets['status_light'] is not None:
                                if plc_bit_set:
                                    # PLC bit is set - flash between red and green
                                    flash_counter = (flash_counter + 1) % 4
                                    if flash_counter < 2:
                                        self.root.after(0, lambda w=widgets['status_light']: self.safe_widget_update(w, bg='red'))
                                    else:
                                        self.root.after(0, lambda w=widgets['status_light']: self.safe_widget_update(w, bg='green'))
                                else:
                                    # No issues - show steady green
                                    self.root.after(0, lambda w=widgets['status_light']: self.safe_widget_update(w, bg='green'))
                            
                            # Monitor operations data for background flashing (excluding gear)
                            has_red_params = False
                            
                            # Read Gear first to determine gas sub color logic
                            gear_result = client.read_holding_registers(address=270, count=1)
                            gear_display = "N"
                            if not gear_result.isError():
                                gear_value = gear_result.registers[0]
                                gear_display = str(gear_value) if 1 <= gear_value <= 9 else "N"
                            
                            # Read Gas Sub %
                            gas_sub_result = client.read_holding_registers(address=250, count=1)
                            if not gas_sub_result.isError():
                                gas_sub_value = gas_sub_result.registers[0]
                                if gear_display != "N" and gas_sub_value == 0:
                                    has_red_params = True
                            
                            # Read RPM
                            rpm_result = client.read_holding_registers(address=370, count=1)
                            if not rpm_result.isError():
                                rpm_value = rpm_result.registers[0]
                                if rpm_value == 0:
                                    has_red_params = True
                            
                            # Flash background if any parameter is red (excluding gear)
                            if has_red_params and unit_frame:
                                if unit.get('alert_acknowledged', False):
                                    # Acknowledged - keep solid red
                                    self.root.after(0, lambda f=unit_frame: self.safe_widget_update(f, bg='#800000'))
                                else:
                                    # Not acknowledged - flash between red and normal
                                    widgets['bg_flash_state'] = not widgets.get('bg_flash_state', False)
                                    if widgets['bg_flash_state']:
                                        self.root.after(0, lambda f=unit_frame: self.safe_widget_update(f, bg='#ff0000'))
                                    else:
                                        self.root.after(0, lambda f=unit_frame: self.safe_widget_update(f, bg='#2d2d2d'))
                            else:
                                # All values are green - reset to normal and clear acknowledged state
                                if unit_frame:
                                    self.root.after(0, lambda f=unit_frame: self.safe_widget_update(f, bg='#2d2d2d'))
                                unit['alert_acknowledged'] = False  # Reset acknowledged state
                        else:
                            # 230xx unit maintenance monitoring - original registers
                            # Read Turbo Temp (address: 302075)
                            turbo_result = client.read_input_registers(address=2075, count=1)
                            if not turbo_result.isError():
                                turbo_temp = turbo_result.registers[0]
                                self.root.after(0, lambda w=widgets['turbo_value'], v=turbo_temp: self.safe_widget_update(w, text=f"{v:>4}"))
                            
                            # Read Battery % (address: 302027)
                            battery_result = client.read_input_registers(address=2027, count=1)
                            has_red_params = False  # Track if any parameter is red
                            if not battery_result.isError():
                                battery_value = battery_result.registers[0]
                                
                                # Check if battery is low (below 50%)
                                if battery_value < 50:
                                    # Flash battery widget background for low battery warning
                                    flash_counter = (flash_counter + 1) % 4
                                    if flash_counter < 2:  # Alternate every 2 cycles
                                        # Red background flash
                                        self.root.after(0, lambda w=widgets['battery_value'], v=battery_value: 
                                                       self.safe_widget_update(w, text=f"{v:>3}", fg="white", bg="#ff0000"))
                                    else:
                                        # Normal background
                                        self.root.after(0, lambda w=widgets['battery_value'], v=battery_value: 
                                                       self.safe_widget_update(w, text=f"{v:>3}", fg="white", bg="#1e1e1e"))
                                else:
                                    # Normal display for healthy battery
                                    self.root.after(0, lambda w=widgets['battery_value'], v=battery_value: 
                                                   self.safe_widget_update(w, text=f"{v:>3}", fg="white", bg="#1e1e1e"))
                                
                            # Read current value from register 401212 (only if maintenance mode or master maintenance mode is active)
                            if (self.maintenance_mode_active or self.master_maintenance_mode) and widgets['setpoint_value'] is not None:
                                setting_result = client.read_holding_registers(address=1212, count=1)
                                if not setting_result.isError():
                                    current_setting = setting_result.registers[0]
                                    # Update the setpoint display with current value
                                    self.root.after(0, lambda w=widgets['setpoint_value'], v=current_setting: self.safe_widget_update(w, text=f"{v:>3}"))
                            
                        # Auto-control and status logic only for 230xx units
                        if not is_lfpc:
                            # Check for auto-control trigger condition - activate fan if turbo temp >= turbo_temp_threshold
                            if self.auto_control_active and turbo_temp >= self.turbo_temp_threshold:
                                # Check if enough time has passed since last fan activation for this unit
                                current_time = time.time()
                                last_activation = self.last_fan_activation.get(ip, 0)
                                
                                # Only send fan command if 10 seconds have passed since last activation
                                if current_time - last_activation >= 10.0:
                                    print(f"Auto-control triggered: Fan activation for {unit_name} - Turbo temp: {turbo_temp}")
                                    # Trigger the fan button (send 100 to register 401000)
                                    register_address = 1000 # Address for 401000
                                    
                                    # Send 100 to register 401000 when temp threshold is reached
                                    fan_result = client.write_register(address=register_address, value=100)
                                    if not fan_result.isError():
                                        print(f"Successfully activated fan for {unit_name} due to high temperature ({turbo_temp})")
                                        # Update the last activation time for this unit
                                        self.last_fan_activation[ip] = current_time
                                    else:
                                        print(f"Error activating fan for {unit_name}: {fan_result}")
                                else:
                                    # Still above threshold but within 10-second cooldown
                                    remaining_time = 10.0 - (current_time - last_activation)
                                    print(f"Auto-control cooldown for {unit_name}: {remaining_time:.1f}s remaining (Temp: {turbo_temp})")
                            
                            # Read and update combined status indicator
                            # Check 300005.02 (bit 2 of register 5)
                            plc_result = client.read_input_registers(address=5, count=1)
                            plc_bit_set = False
                            
                            if not plc_result.isError():
                                plc_bit_set = bool(plc_result.registers[0] & 0x04)  # Check bit 2
                            
                            # Update the combined status indicator
                            if plc_bit_set:
                                # PLC bit is set - flash between red and green
                                flash_counter = (flash_counter + 1) % 4
                                if flash_counter < 2:  # Alternate every 2 cycles
                                    self.root.after(0, lambda w=widgets['status_light']: self.safe_widget_update(w, bg='red'))
                                else:
                                    self.root.after(0, lambda w=widgets['status_light']: self.safe_widget_update(w, bg='green'))
                            else:
                                # No issues - show steady green
                                self.root.after(0, lambda w=widgets['status_light']: self.safe_widget_update(w, bg='green'))

                            # Read control value from holding register 401000 (address 1000)
                            response = client.read_holding_registers(address=1000, count=1)
                            if not response.isError():
                                control_value = response.registers[0]
                                # For register 401000: value 100 = ON, make fan button flash red
                                if control_value == 100:
                                    # Flash the fan button red when 401000 = 100
                                    flash_counter = (flash_counter + 1) % 4
                                    if flash_counter < 2:  # Alternate every 2 cycles
                                        self.root.after(0, lambda w=widgets['control_button']: self.safe_widget_update(w, bg='red'))
                                    else:
                                        self.root.after(0, lambda w=widgets['control_button']: self.safe_widget_update(w, bg='#d83b01'))  # Darker red
                                else:
                                    # Normal blue color when 401000 = 0
                                    self.root.after(0, lambda w=widgets['control_button']: self.safe_widget_update(w, bg='#0078d4'))
                            
                            # Monitor operations data for background flashing (excluding gear)
                            has_red_params = False
                            
                            # Read Engine RPM
                            rpm_result = client.read_holding_registers(address=370, count=1)
                            if not rpm_result.isError():
                                rpm_value = rpm_result.registers[0]
                                if rpm_value < 1200:
                                    has_red_params = True
                            
                            # Read Envolts State
                            envolts_result = client.read_input_registers(address=2044, count=1)
                            if not envolts_result.isError():
                                envolts_value = envolts_result.registers[0]
                                if envolts_value != 5:
                                    has_red_params = True
                            
                            # Read PE Oil Rate
                            pe_oil_result = client.read_holding_registers(address=494, count=2)
                            if not pe_oil_result.isError():
                                import struct
                                combined_value = (pe_oil_result.registers[0] << 16) | pe_oil_result.registers[1]
                                pe_oil_value = struct.unpack('>f', struct.pack('>I', combined_value))[0]
                                if pe_oil_value < 34:
                                    has_red_params = True
                            
                            # Read GB Oil Rate
                            gb_oil_result = client.read_input_registers(address=2033, count=2)
                            if not gb_oil_result.isError():
                                import struct
                                combined_value = (gb_oil_result.registers[0] << 16) | gb_oil_result.registers[1]
                                gb_oil_value = struct.unpack('>f', struct.pack('>I', combined_value))[0]
                                if gb_oil_value < 34:
                                    has_red_params = True
                            
                            # Read Gas PSI
                            gas_psi_result = client.read_input_registers(address=2035, count=1)
                            if not gas_psi_result.isError():
                                gas_psi_value = gas_psi_result.registers[0]
                                if gas_psi_value < 100:  # Red or amber
                                    has_red_params = True
                            
                            # Flash background if any parameter is red (excluding gear)
                            if has_red_params and unit_frame:
                                if unit.get('alert_acknowledged', False):
                                    # Acknowledged - keep solid red
                                    self.root.after(0, lambda f=unit_frame: self.safe_widget_update(f, bg='#800000'))
                                else:
                                    # Not acknowledged - flash between red and normal
                                    widgets['bg_flash_state'] = not widgets.get('bg_flash_state', False)
                                    if widgets['bg_flash_state']:
                                        self.root.after(0, lambda f=unit_frame: self.safe_widget_update(f, bg='#ff0000'))
                                    else:
                                        self.root.after(0, lambda f=unit_frame: self.safe_widget_update(f, bg='#2d2d2d'))
                            else:
                                # All values are green - reset to normal and clear acknowledged state
                                if unit_frame:
                                    self.root.after(0, lambda f=unit_frame: self.safe_widget_update(f, bg='#2d2d2d'))
                                unit['alert_acknowledged'] = False  # Reset acknowledged state
                except Exception as e:
                    print(f"Error in monitor loop for {unit_name}: {e}")
                    # Reset displays on error
                    self.root.after(0, lambda w=widgets['turbo_value']: self.safe_widget_update(w, text="---"))
                    self.root.after(0, lambda w=widgets['battery_value']: self.safe_widget_update(w, text="---"))
                    if widgets['setpoint_value'] is not None:
                        self.root.after(0, lambda w=widgets['setpoint_value']: self.safe_widget_update(w, text="---"))
                    self.root.after(0, lambda w=widgets['status_light']: self.safe_widget_update(w, bg='gray'))
                    # Reset fan button color on error
                    self.root.after(0, lambda w=widgets['control_button']: self.safe_widget_update(w, bg='#0078d4'))
                finally:
                    # Always ensure the client is closed
                    try:
                        client.close()
                    except Exception as e:
                        print(f"Error closing Modbus client for {unit_name}: {e}")

                # Check again if monitoring is still active before sleeping
                if not self.monitoring_active:
                    print(f"Monitoring deactivated for {unit_name} during iteration, exiting")
                    break
                    
                # Sleep between polling cycles - 1500ms update rate
                time.sleep(1.5)  # Exactly 1500ms

        except Exception as e:
            print(f"Error in monitor thread for {unit['unit_name']}: {e}")

    def open_unit_operations_window(self, unit):
        """Open a popup window showing live monitor and operations data for the selected unit"""
        unit_name = unit['unit_name']
        ip_address = unit['ip_address']
        is_lfpc = unit.get('unit_type') == 'LFPC'
        
        # Create popup window with larger size to accommodate all data
        popup = tk.Toplevel(self.root)
        popup.title(f"Unit Overview - {unit_name}")
        popup.geometry("550x800" if not is_lfpc else "500x400")
        popup.configure(bg='#1e1e1e')
        popup.transient(self.root)
        
        # Header
        header_label = tk.Label(
            popup,
            text=f"{unit_name} - Unit Overview",
            font=("Segoe UI", 18, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.pack(pady=10)
        
        ip_label = tk.Label(
            popup,
            text=f"IP: {ip_address}",
            font=("Segoe UI", 12),
            bg='#1e1e1e',
            fg='#aaaaaa'
        )
        ip_label.pack(pady=5)
        
        separator = ttk.Separator(popup, orient='horizontal')
        separator.pack(fill='x', padx=20, pady=10)
        
        # Create main container for data (no scrollbar needed with larger window)
        data_container = tk.Frame(popup, bg='#1e1e1e')
        data_container.pack(fill='both', expand=True, padx=20, pady=10)
        
        # Data display frame
        data_frame = tk.Frame(data_container, bg='#1e1e1e')
        data_frame.pack(fill='both', expand=True)
        
        popup_widgets = {}
        
        if is_lfpc:
            # LFPC unit: Gas Sub %, Load %, RPM, Gear
            # Gas Sub %
            gas_sub_frame = tk.Frame(data_frame, bg='#1e1e1e')
            gas_sub_frame.pack(fill='x', pady=8)
            tk.Label(gas_sub_frame, text="Gas Sub %:", font=("Segoe UI", 12, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            gas_sub_value = tk.Label(gas_sub_frame, text="---", font=("Segoe UI", 14, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            gas_sub_value.pack(side='right', padx=5)
            popup_widgets['gas_sub_value'] = gas_sub_value
            
            # Load %
            load_frame = tk.Frame(data_frame, bg='#1e1e1e')
            load_frame.pack(fill='x', pady=8)
            tk.Label(load_frame, text="Load %:", font=("Segoe UI", 12, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            load_value = tk.Label(load_frame, text="---", font=("Segoe UI", 14, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            load_value.pack(side='right', padx=5)
            popup_widgets['load_value'] = load_value
            
            # RPM
            rpm_frame = tk.Frame(data_frame, bg='#1e1e1e')
            rpm_frame.pack(fill='x', pady=8)
            tk.Label(rpm_frame, text="RPM:", font=("Segoe UI", 12, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            rpm_value = tk.Label(rpm_frame, text="---", font=("Segoe UI", 14, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            rpm_value.pack(side='right', padx=5)
            popup_widgets['rpm_value'] = rpm_value
            
            # Gear
            gear_frame = tk.Frame(data_frame, bg='#1e1e1e')
            gear_frame.pack(fill='x', pady=8)
            tk.Label(gear_frame, text="Gear:", font=("Segoe UI", 12, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            gear_value = tk.Label(gear_frame, text="---", font=("Segoe UI", 14, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            gear_value.pack(side='right', padx=5)
            popup_widgets['gear_value'] = gear_value
            
        else:
            # Prime (230xx) unit: Show Monitor Data first, then Operations Data
            
            # === MONITOR DATA SECTION ===
            monitor_header = tk.Label(
                data_frame,
                text="Monitor Data",
                font=("Segoe UI", 14, "bold"),
                bg='#1e1e1e',
                fg='#0078d4'
            )
            monitor_header.pack(pady=(0, 10), anchor='w')
            
            # Turbo Temp
            turbo_frame = tk.Frame(data_frame, bg='#1e1e1e')
            turbo_frame.pack(fill='x', pady=6)
            tk.Label(turbo_frame, text="Turbo Temp:", font=("Segoe UI", 11, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            turbo_value = tk.Label(turbo_frame, text="---", font=("Segoe UI", 13, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            turbo_value.pack(side='right', padx=5)
            popup_widgets['turbo_value'] = turbo_value
            
            # Battery %
            battery_frame = tk.Frame(data_frame, bg='#1e1e1e')
            battery_frame.pack(fill='x', pady=6)
            tk.Label(battery_frame, text="Battery %:", font=("Segoe UI", 11, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            battery_value = tk.Label(battery_frame, text="---", font=("Segoe UI", 13, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            battery_value.pack(side='right', padx=5)
            popup_widgets['battery_value'] = battery_value
            
            # Separator between sections
            ttk.Separator(data_frame, orient='horizontal').pack(fill='x', pady=15)
            
            # === OPERATIONS DATA SECTION ===
            operations_header = tk.Label(
                data_frame,
                text="Operations Data",
                font=("Segoe UI", 14, "bold"),
                bg='#1e1e1e',
                fg='#0078d4'
            )
            operations_header.pack(pady=(0, 10), anchor='w')
            
            # Env State
            env_frame = tk.Frame(data_frame, bg='#1e1e1e')
            env_frame.pack(fill='x', pady=6)
            tk.Label(env_frame, text="Env State:", font=("Segoe UI", 11, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            envolts_value = tk.Label(env_frame, text="---", font=("Segoe UI", 13, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            envolts_value.pack(side='right', padx=5)
            popup_widgets['envolts_value'] = envolts_value
            
            # RPM
            rpm_frame = tk.Frame(data_frame, bg='#1e1e1e')
            rpm_frame.pack(fill='x', pady=6)
            tk.Label(rpm_frame, text="RPM:", font=("Segoe UI", 11, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            rpm_value = tk.Label(rpm_frame, text="---", font=("Segoe UI", 13, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            rpm_value.pack(side='right', padx=5)
            popup_widgets['rpm_value'] = rpm_value
            
            # PE Oil Rate (High Rate)
            pe_frame = tk.Frame(data_frame, bg='#1e1e1e')
            pe_frame.pack(fill='x', pady=6)
            tk.Label(pe_frame, text="High Rate:", font=("Segoe UI", 11, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            pe_oil_value = tk.Label(pe_frame, text="---", font=("Segoe UI", 13, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            pe_oil_value.pack(side='right', padx=5)
            popup_widgets['pe_oil_value'] = pe_oil_value
            
            # GB Oil Rate (Low Rate)
            gb_frame = tk.Frame(data_frame, bg='#1e1e1e')
            gb_frame.pack(fill='x', pady=6)
            tk.Label(gb_frame, text="Low Rate:", font=("Segoe UI", 11, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            gb_oil_value = tk.Label(gb_frame, text="---", font=("Segoe UI", 13, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            gb_oil_value.pack(side='right', padx=5)
            popup_widgets['gb_oil_value'] = gb_oil_value
            
            # Gas PSI
            gas_frame = tk.Frame(data_frame, bg='#1e1e1e')
            gas_frame.pack(fill='x', pady=6)
            tk.Label(gas_frame, text="Gas PSI:", font=("Segoe UI", 11, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            gas_psi_value = tk.Label(gas_frame, text="---", font=("Segoe UI", 13, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            gas_psi_value.pack(side='right', padx=5)
            popup_widgets['gas_psi_value'] = gas_psi_value
            
            # Gear
            gear_frame = tk.Frame(data_frame, bg='#1e1e1e')
            gear_frame.pack(fill='x', pady=6)
            tk.Label(gear_frame, text="Gear:", font=("Segoe UI", 11, "bold"), bg='#1e1e1e', fg='white', width=15, anchor='w').pack(side='left', padx=5)
            gear_value = tk.Label(gear_frame, text="---", font=("Segoe UI", 13, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=2, width=10)
            gear_value.pack(side='right', padx=5)
            popup_widgets['gear_value'] = gear_value
            
            # Indicators frame
            indicators_frame = tk.Frame(data_frame, bg='#1e1e1e')
            indicators_frame.pack(fill='x', pady=15)
            tk.Label(indicators_frame, text="Indicators:", font=("Segoe UI", 12, "bold"), bg='#1e1e1e', fg='white').pack(anchor='w', padx=5, pady=5)
            
            ind_display_frame = tk.Frame(indicators_frame, bg='#1e1e1e')
            ind_display_frame.pack(fill='x', padx=20)
            
            # V1 indicator
            v1_frame = tk.Frame(ind_display_frame, bg='#1e1e1e')
            v1_frame.pack(side='left', expand=True)
            v1_indicator = tk.Label(v1_frame, text="●", font=("Segoe UI", 20, "bold"), bg='#1e1e1e', fg='gray')
            v1_indicator.pack()
            tk.Label(v1_frame, text="V1", font=("Segoe UI", 10), bg='#1e1e1e', fg='white').pack()
            popup_widgets['v1_indicator'] = v1_indicator
            
            # V2 indicator
            v2_frame = tk.Frame(ind_display_frame, bg='#1e1e1e')
            v2_frame.pack(side='left', expand=True)
            v2_indicator = tk.Label(v2_frame, text="●", font=("Segoe UI", 20, "bold"), bg='#1e1e1e', fg='gray')
            v2_indicator.pack()
            tk.Label(v2_frame, text="V2", font=("Segoe UI", 10), bg='#1e1e1e', fg='white').pack()
            popup_widgets['v2_indicator'] = v2_indicator
            
            # GLT indicator
            glt_frame = tk.Frame(ind_display_frame, bg='#1e1e1e')
            glt_frame.pack(side='left', expand=True)
            glt_indicator = tk.Label(glt_frame, text="●", font=("Segoe UI", 20, "bold"), bg='#1e1e1e', fg='gray')
            glt_indicator.pack()
            tk.Label(glt_frame, text="GLT", font=("Segoe UI", 10), bg='#1e1e1e', fg='white').pack()
            popup_widgets['glt_indicator'] = glt_indicator
        
        # Start monitoring for this popup (before close button)
        popup_monitor_active = {'active': True, 'gas_psi_flash_state': False}  # For gas PSI flashing
        
        # Button container frame
        button_frame = tk.Frame(popup, bg='#1e1e1e')
        button_frame.pack(pady=15)
        
        # Acknowledge button (only show if box is flashing red)
        def acknowledge_alert():
            """Acknowledge the red alert - stop flashing and keep solid red until values are green"""
            unit['alert_acknowledged'] = True
            ack_button.pack_forget()  # Hide the acknowledge button
        
        ack_button = HoverButton(
            button_frame,
            text="Acknowledge",
            width=15,
            font=("Segoe UI", 11, "bold"),
            bg="#ff8800",
            fg="white",
            relief="flat",
            hover_color="#ffaa00",
            command=acknowledge_alert
        )
        
        # Only show acknowledge button if box is currently flashing
        if unit.get('widgets', {}).get('bg_flash_state', False) or unit.get('bg_flash_state', False):
            ack_button.pack(side='left', padx=5)
        
        # Close button
        close_button = HoverButton(
            button_frame,
            text="Close",
            width=15,
            font=("Segoe UI", 11, "bold"),
            bg="#d83b01",
            fg="white",
            relief="flat",
            hover_color="#e85b24",
            command=lambda: self.close_popup_window(popup, popup_monitor_active)
        )
        close_button.pack(side='left', padx=5)
        
        def monitor_popup():
            """Monitor operations data for the popup window"""
            import struct
            print(f"Starting popup monitoring for {unit_name} at {ip_address}")
            
            def safe_popup_update(widget, **kwargs):
                """Safely update popup widgets from monitoring thread"""
                def update_widget():
                    if widget and popup.winfo_exists():
                        self.safe_widget_update(widget, **kwargs)
                if popup.winfo_exists():
                    popup.after(0, update_widget)
            
            # Connect once at the start
            client = ModbusTcpClient(ip_address)
            if not client.connect():
                print(f"Failed to connect to {unit_name} at {ip_address} for popup monitoring")
                return
            
            print(f"Popup monitor connected to {unit_name}")
            
            while popup_monitor_active['active']:
                try:
                    if not popup.winfo_exists():
                        popup_monitor_active['active'] = False
                        print(f"Popup closed for {unit_name}, stopping monitoring")
                        break
                    
                    if is_lfpc:
                        # LFPC monitoring
                        gear_result = client.read_holding_registers(address=270, count=1)
                        gear_display = "N"
                        if not gear_result.isError():
                            gear_value_num = gear_result.registers[0]
                            gear_display = str(gear_value_num) if 1 <= gear_value_num <= 9 else "N"
                            gear_color = '#ff0000' if gear_display == "N" else 'white'
                            safe_popup_update(popup_widgets.get('gear_value'), text=gear_display, fg=gear_color)
                        
                        gas_sub_result = client.read_holding_registers(address=250, count=1)
                        if not gas_sub_result.isError():
                            gas_sub_val = gas_sub_result.registers[0]
                            if gear_display != "N" and gas_sub_val == 0:
                                gas_sub_color = '#ff0000'
                            else:
                                gas_sub_color = '#00ff00'
                            safe_popup_update(popup_widgets.get('gas_sub_value'), text=f"{gas_sub_val}%", fg=gas_sub_color)
                        
                        load_result = client.read_holding_registers(address=373, count=1)
                        if not load_result.isError():
                            load_val = load_result.registers[0]
                            safe_popup_update(popup_widgets.get('load_value'), text=f"{load_val}%")
                        
                        rpm_result = client.read_holding_registers(address=370, count=1)
                        if not rpm_result.isError():
                            rpm_val = rpm_result.registers[0]
                            rpm_color = '#ff0000' if rpm_val == 0 else '#00ff00'
                            safe_popup_update(popup_widgets.get('rpm_value'), text=str(rpm_val), fg=rpm_color)
                    
                    else:
                        # Prime (230xx) monitoring
                        
                        # Monitor Data - Turbo Temp (register 302075)
                        turbo_result = client.read_input_registers(address=2075, count=1)
                        if not turbo_result.isError():
                            turbo_val = turbo_result.registers[0]
                            turbo_color = '#ff0000' if turbo_val >= 1050 else '#00ff00'
                            safe_popup_update(popup_widgets.get('turbo_value'), text=str(turbo_val), fg=turbo_color)
                        
                        # Monitor Data - Battery %
                        battery_result = client.read_input_registers(address=2027, count=1)
                        if not battery_result.isError():
                            battery_val = battery_result.registers[0]
                            if battery_val < 20:
                                battery_color = '#ff0000'
                            elif battery_val < 50:
                                battery_color = '#ffaa00'
                            else:
                                battery_color = '#00ff00'
                            safe_popup_update(popup_widgets.get('battery_value'), text=f"{battery_val}%", fg=battery_color)
                        
                        # Operations Data - RPM from register 40370
                        rpm_result = client.read_holding_registers(address=370, count=1)
                        if not rpm_result.isError():
                            rpm_val = rpm_result.registers[0]
                            rpm_color = '#ff0000' if rpm_val < 1200 else '#00ff00'
                            safe_popup_update(popup_widgets.get('rpm_value'), text=str(rpm_val), fg=rpm_color)
                        
                        envolts_result = client.read_input_registers(address=2044, count=1)
                        if not envolts_result.isError():
                            envolts_val = envolts_result.registers[0]
                            envolts_color = '#00ff00' if envolts_val == 5 else '#ff0000'
                            safe_popup_update(popup_widgets.get('envolts_value'), text=str(envolts_val), fg=envolts_color)
                        
                        pe_oil_result = client.read_holding_registers(address=494, count=2)
                        if not pe_oil_result.isError():
                            combined_value = (pe_oil_result.registers[0] << 16) | pe_oil_result.registers[1]
                            pe_oil_val = struct.unpack('>f', struct.pack('>I', combined_value))[0]
                            pe_oil_color = '#ff0000' if pe_oil_val < 34 else '#00ff00'
                            safe_popup_update(popup_widgets.get('pe_oil_value'), text=f"{pe_oil_val:.2f}", fg=pe_oil_color)
                        
                        gb_oil_result = client.read_input_registers(address=2033, count=2)
                        if not gb_oil_result.isError():
                            combined_value = (gb_oil_result.registers[0] << 16) | gb_oil_result.registers[1]
                            gb_oil_val = struct.unpack('>f', struct.pack('>I', combined_value))[0]
                            gb_oil_color = '#ff0000' if gb_oil_val < 34 else '#00ff00'
                            safe_popup_update(popup_widgets.get('gb_oil_value'), text=f"{gb_oil_val:.2f}", fg=gb_oil_color)
                        
                        gas_psi_result = client.read_input_registers(address=2035, count=1)
                        if not gas_psi_result.isError():
                            gas_psi_val = gas_psi_result.registers[0]
                            if gas_psi_val < 85:
                                popup_monitor_active['gas_psi_flash_state'] = not popup_monitor_active.get('gas_psi_flash_state', False)
                                gas_psi_color = '#ff0000' if popup_monitor_active['gas_psi_flash_state'] else '#800000'
                            elif gas_psi_val < 100:
                                popup_monitor_active['gas_psi_flash_state'] = not popup_monitor_active.get('gas_psi_flash_state', False)
                                gas_psi_color = '#ffaa00' if popup_monitor_active['gas_psi_flash_state'] else '#cc8800'
                            else:
                                gas_psi_color = '#00ff00'
                            safe_popup_update(popup_widgets.get('gas_psi_value'), text=str(gas_psi_val), fg=gas_psi_color)
                        
                        gear_result = client.read_holding_registers(address=270, count=1)
                        if not gear_result.isError():
                            gear_val = gear_result.registers[0]
                            gear_display = str(gear_val) if 1 <= gear_val <= 9 else "N"
                            gear_color = '#ff0000' if gear_display == "N" else 'white'
                            safe_popup_update(popup_widgets.get('gear_value'), text=gear_display, fg=gear_color)
                        
                        # Indicators
                        v1_result = client.read_input_registers(address=2002, count=1)
                        if not v1_result.isError():
                            v1_state = bool(v1_result.registers[0] & (1 << 5))
                            color = '#00ff00' if v1_state else 'gray'
                            safe_popup_update(popup_widgets.get('v1_indicator'), fg=color)
                        
                        v2_result = client.read_input_registers(address=2002, count=1)
                        if not v2_result.isError():
                            v2_state = bool(v2_result.registers[0] & (1 << 6))
                            color = '#00ff00' if v2_state else 'gray'
                            safe_popup_update(popup_widgets.get('v2_indicator'), fg=color)
                        
                        glt_result = client.read_input_registers(address=2002, count=1)
                        if not glt_result.isError():
                            glt_state = bool(glt_result.registers[0] & (1 << 7))
                            color = '#00ff00' if glt_state else 'gray'
                            safe_popup_update(popup_widgets.get('glt_indicator'), fg=color)
                except Exception as e:
                    print(f"Error in popup monitor for {unit_name}: {e}")
                    import traceback
                    traceback.print_exc()
                
                time.sleep(2)  # Update every 2 seconds
            
            # Close connection when monitoring stops
            try:
                client.close()
                print(f"Popup monitor disconnected from {unit_name}")
            except:
                pass
        
        # Start monitoring thread
        monitor_thread = threading.Thread(target=monitor_popup, daemon=True)
        monitor_thread.start()
        print(f"Popup monitoring thread started for {unit_name}")
    
    def close_popup_window(self, popup, monitor_active):
        """Close the popup window and stop its monitoring thread"""
        monitor_active['active'] = False
        popup.destroy()
    
    def toggle_auto_control(self):
        """Toggle the auto control feature"""
        self.auto_control_active = not self.auto_control_active
        
        if self.auto_control_active:
            # Change button appearance to indicate active state
            self.auto_button.config(text="Auto Fan ON", bg="#107c10")  # Green when active
            self.auto_button.hover_color = "#25902a"  # Update hover color
            
            # Auto-start monitoring if not already running
            if not self.monitoring_active:
                self.start_monitoring()
        else:
            # Reset to inactive appearance
            self.auto_button.config(text="Auto Fan OFF", bg="#0078d4")  # Blue when inactive
            self.auto_button.hover_color = "#2b88d8"  # Update hover color
    
    def toggle_control(self, unit):
        """Send value 100 to the control register (401000)"""
        ip = unit['ip_address']
        client = ModbusTcpClient(ip)
        
        try:
            # Address 401000 (subtract 400000 for Modbus register address)
            register_address = 1000  # Register address for 401000
            
            # Always send 100 to the register
            result = client.write_register(address=register_address, value=100)
            
            if result.isError():
                print(f"Error writing to register 401000 for {unit['unit_name']}: {result}")
            else:
                print(f"Successfully sent value 100 to register 401000 for {unit['unit_name']}")
                
        finally:
            client.close()
    
    def send_register_value(self, unit, value_var, register_offset):
        """Send the value from an input field to the specified register address
        and also set address 301548 to true
        
        Args:
            unit: The unit dictionary containing IP information
            value_var: StringVar containing the value to send
            register_offset: The register offset (for 401212, this would be 1212)
        """
        try:
            # Get the value from the StringVar
            value_str = value_var.get().strip()
            
            # Validate value is a number and within allowed range
            if not value_str.isdigit():
                messagebox.showerror("Invalid Input", f"Value must be a number (received '{value_str}')")
                return
                
            value = int(value_str)
            # Enforce safe numeric range for setpoints (50-100%)
            if value < 50 or value > 100:
                messagebox.showerror("Invalid Input", f"Setpoint must be between 50-100% (received {value})")
                return
            
            # Connect to Modbus and write the value
            ip = unit['ip_address']
            client = ModbusTcpClient(ip)
            
            if client.connect():
                # First set register 400509 to value 3
                result_509 = client.write_register(address=509, value=3)
                
                if result_509.isError():
                    print(f"Error setting register 400509 to 3 for {unit['unit_name']}: {result_509}")
                    client.close()
                    return
                else:
                    print(f"Successfully set register 400509 to 3 for {unit['unit_name']}")
                
                # Then write the value to the main register (401212)
                result = client.write_register(address=register_offset, value=value)
                
                if result.isError():
                    print(f"Error writing to register {register_offset+400000} for {unit['unit_name']}: {result}")
                else:
                    print(f"Successfully wrote value {value} to register {register_offset+400000} for {unit['unit_name']}")
                    # Clear the input box after successful write
                    self.root.after(0, lambda var=value_var: var.set(""))
            else:
                print(f"Failed to connect to {unit['unit_name']} at {ip}")
                
            client.close()
            
        except Exception as e:
            print(f"Error in send_register_value: {e}")
    
    def back_to_main(self):
        """Stop monitoring before returning to the main configuration page"""
        print("Navigation requested: Back to main configuration page")
        
        # Reset monitoring state tracking when navigating to main page
        self.was_monitoring_before_navigation = False
        
        # Deactivate auto fan when navigating away from monitor page
        if self.auto_control_active:
            print("Deactivating auto fan control due to navigation")
            self.auto_control_active = False
        
        # First stop all monitoring with a confirmation message
        if self.monitoring_active:
            print("Stopping active monitoring before navigation")
            self.stop_monitoring()
            
            # Double check that all threads have indeed stopped or are stopping
            active_count = sum(1 for thread in self.monitor_threads if thread.is_alive())
            if active_count > 0:
                print(f"Warning: {active_count} monitoring threads still active during navigation")
                
        # Ensure monitor_threads list is cleared
        self.monitor_threads = []
        
        # Then return to main page
        self.load_existing_configuration()
    
    def launch_unit_hmi(self, unit):
        """Launch the HMI executable for the selected unit"""
        unit_name = unit['unit_name']
        folder_path = unit['folder_path']
        
        # Find the executable in the unit's folder
        exe_file = f"{unit_name}.exe"
        exe_path = os.path.join(folder_path, exe_file)
        
        if os.path.exists(exe_path):
            # Similar to set_pump_assignment, kill other HMI processes first
            try:
                # Get list of running processes with their executable names
                process_list = subprocess.check_output(['tasklist', '/FO', 'CSV', '/NH'],
                                                      universal_newlines=True).split('\n')

                # Get basenames of all exe files except the target
                target_exe = os.path.basename(exe_path)
                exe_basenames = [os.path.basename(exe) for exe in self.get_exe_files() if os.path.basename(exe) != target_exe]

                # Kill each running process that matches our exe files
                for process in process_list:
                    if process:  # Skip empty lines
                        try:
                            process_name = process.split(',')[0].strip('"')
                            if process_name in exe_basenames:
                                subprocess.run(['taskkill', '/F', '/IM', process_name],
                                              stdout=subprocess.DEVNULL,
                                              stderr=subprocess.DEVNULL)
                                time.sleep(0.1)  # Small delay to ensure process is killed
                        except Exception as e:
                            print(f"Error killing process {process_name}: {e}")
            except Exception as e:
                print(f"Error killing existing processes: {e}")
            
            # Launch the executable
            try:
                subprocess.Popen(exe_path)
            except Exception as e:
                print(f"Error launching HMI for unit {unit_name}: {e}")
                messagebox.showerror("Launch Error", f"Could not launch HMI for unit {unit_name}\n\nError: {e}")
        else:
            messagebox.showerror("File Not Found", f"HMI executable for unit {unit_name} not found at:\n{exe_path}")
            
    def create_operations_page(self):
        """Create the Operations monitoring page with specified Modbus addresses"""
        # Track current monitoring state before stopping
        self.was_monitoring_before_navigation = self.monitoring_active
        
        # Stop any existing monitor threads
        self.stop_monitoring()
        
        if self.current_frame:
            self.current_frame.destroy()

        # Set up the main frame
        self.current_frame = tk.Frame(self.root)
        self.current_frame.configure(bg='#1e1e1e')
        self.current_frame.pack(expand=True, fill='both', padx=30, pady=20)
        
        # Modern header with subtle bottom border
        header_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        header_frame.pack(fill='x', pady=(0, 5))
        
        header_label = tk.Label(
            header_frame,
            text="Operations Monitor",
            font=("Segoe UI", 26, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.pack(pady=(0, 5))
        
        separator = ttk.Separator(header_frame, orient='horizontal')
        separator.pack(fill='x', padx=50)
        
        # Find 230xx and LFPC folders and read their IP addresses
        self.units_info = self.find_230xx_folders() + self.find_lfpc_folders()
        
        if not self.units_info:
            # Create a placeholder frame for consistent layout
            placeholder_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
            placeholder_frame.pack(expand=True, fill='both')
            
            no_units_label = tk.Label(
                placeholder_frame,
                text="No 230xx or LFPC units found. Please scan for units first.",
                font=("Segoe UI", 16),
                bg='#1e1e1e',
                fg='white'
            )
            no_units_label.pack(expand=True, pady=50)
            
            # Modern styled bottom control buttons
            button_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
            button_frame.pack(side='bottom', pady=25)
            
            # Back button
            back_button = HoverButton(
                button_frame,
                text="Back",
                width=15,
                font=("Segoe UI", 12, "bold"),
                bg="#0078d4",
                fg="white",
                relief="flat",
                hover_color="#2b88d8",
                command=self.load_existing_configuration
            )
            back_button.pack(side='left', padx=10, ipady=5)
            return


        
        # Create a frame for the units display with modern styling
        self.grid_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        self.grid_frame.pack(expand=True, fill='both', padx=10, pady=10)
        
        # Create monitor displays for each unit with operations data
        self.create_operations_monitors()
        
        # Modern styled bottom control buttons
        button_frame = tk.Frame(self.current_frame, bg='#1e1e1e', pady=15)
        button_frame.pack(side='bottom', fill='x')
        
        # Start monitoring button
        self.start_button = HoverButton(
            button_frame,
            text="Start Monitoring",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#107c10",
            fg="white",
            relief="flat",
            hover_color="#25902a",
            command=self.start_operations_monitoring
        )
        self.start_button.pack(side='left', padx=10, ipady=5)
        
        # Stop monitoring button
        self.stop_button = HoverButton(
            button_frame,
            text="Stop Monitoring",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#d83b01",
            fg="white",
            relief="flat",
            hover_color="#e85b24",
            command=self.stop_monitoring
        )
        self.stop_button.pack(side='left', padx=10, ipady=5)
        
        # Turbo Monitor button
        turbo_monitor_button = HoverButton(
            button_frame,
            text="Turbo Monitor",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#ff8c00",
            fg="white",
            relief="flat",
            hover_color="#ffa500",
            command=self.create_monitor_page
        )
        turbo_monitor_button.pack(side='left', padx=10, ipady=5)
        
        # Back button
        back_button = HoverButton(
            button_frame,
            text="Back",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#0078d4",
            fg="white",
            relief="flat",
            hover_color="#2b88d8",
            command=self.load_existing_configuration
        )
        back_button.pack(side='left', padx=10, ipady=5)
        
        # Auto-start monitoring if it was active before navigation
        if self.was_monitoring_before_navigation:
            self.root.after(100, self.start_operations_monitoring)  # Delay to ensure UI is ready

    def create_operations_monitors(self):
        """Create monitoring displays for each unit with operations data"""
        # Load pump assignments to map pump numbers to unit numbers
        pump_assignments = self.load_assignments()
        
        # Create a mapping of unit numbers to their assigned pump numbers
        unit_to_pump_map = {}
        for pump_num, data in pump_assignments.items():
            if data.get('exe_name') != 'Select Pump':
                unit_to_pump_map[data.get('exe_name')] = pump_num
        
        # Sort units based on their pump assignments
        sorted_units = []
        unassigned_units = []
        
        for unit in self.units_info:
            unit_name = unit['unit_name']
            if unit_name in unit_to_pump_map.keys():
                # Add pump number to unit info
                unit['pump_number'] = unit_to_pump_map[unit_name]
                sorted_units.append(unit)
            else:
                # Unit not assigned to any pump
                unit['pump_number'] = None
                unassigned_units.append(unit)
        
        # Sort units by pump number
        sorted_units.sort(key=lambda u: int(u['pump_number']))
        
        # Add unassigned units at the end
        all_units = sorted_units + unassigned_units
        
        # Calculate rows and columns (4 rows per column for better layout)
        rows_per_column = 4
        num_units = len(all_units)
        num_columns = (num_units + rows_per_column - 1) // rows_per_column
        
        for i, unit in enumerate(all_units):
            # Calculate position (column first, then row)
            col = i // rows_per_column
            row = i % rows_per_column
            
            # Create a frame for this unit (larger for operations data)
            unit_frame = tk.Frame(self.grid_frame, bg='#2d2d2d', padx=10, pady=10, bd=1, relief='solid', width=280, height=200)
            unit_frame.grid(row=row, column=col, padx=8, pady=8, sticky='nsew')
            unit_frame.grid_propagate(False)  # Force the frame to maintain its size
            
            # Unit header with name and IP
            header = tk.Frame(unit_frame, bg='#2d2d2d')
            header.pack(fill='x')
            
            # Display format: "Pump # - Unit ###" if pump number exists
            if unit['pump_number'] is not None:
                displayed_pump_num = int(unit['pump_number']) + 1
                label_text = f"Pump {displayed_pump_num} - {unit['unit_name']}"
            else:
                label_text = f" {unit['unit_name']}"
                
            unit_label = tk.Label(
                header,
                text=label_text,
                font=("Segoe UI", 11, "bold"),
                bg='#2d2d2d',
                fg='white'
            )
            unit_label.pack(side='left')
            
            ip_label = tk.Label(
                header,
                text=f"IP: {unit['ip_address']}",
                font=("Segoe UI", 9),
                bg='#2d2d2d',
                fg='#aaaaaa'
            )
            ip_label.pack(side='right')
            
            # Separator
            separator = ttk.Separator(unit_frame, orient='horizontal')
            separator.pack(fill='x', pady=5)
            
            # Operations data frame
            data_frame = tk.Frame(unit_frame, bg='#2d2d2d')
            data_frame.pack(fill='both', expand=True, pady=2)
            
            # Check if this is an LFPC unit
            is_lfpc = unit.get('unit_type') == 'LFPC'
            
            if is_lfpc:
                # LFPC units: Gas Sub %, Load %, RPM
                # First row: Gas Sub % and Load % side by side
                first_row_frame = tk.Frame(data_frame, bg='#2d2d2d')
                first_row_frame.pack(fill='x', pady=2)
                
                # Gas Sub % (left side)
                gas_sub_frame = tk.Frame(first_row_frame, bg='#2d2d2d')
                gas_sub_frame.pack(side='left', fill='x', expand=True, padx=(0, 5))
                gas_sub_label_frame = tk.Frame(gas_sub_frame, bg='#2d2d2d')
                gas_sub_label_frame.pack(fill='x')
                tk.Label(gas_sub_label_frame, text="Gas Sub %:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                gas_sub_value = tk.Label(gas_sub_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                gas_sub_value.pack(side='right')
                
                # Load % (right side)
                load_frame = tk.Frame(first_row_frame, bg='#2d2d2d')
                load_frame.pack(side='right', fill='x', expand=True, padx=(5, 0))
                load_label_frame = tk.Frame(load_frame, bg='#2d2d2d')
                load_label_frame.pack(fill='x')
                tk.Label(load_label_frame, text="Load %:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                load_value = tk.Label(load_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                load_value.pack(side='right')
                
                # Second row: RPM and Gear side by side
                second_row_frame = tk.Frame(data_frame, bg='#2d2d2d')
                second_row_frame.pack(fill='x', pady=2)
                
                # RPM (left side)
                rpm_frame = tk.Frame(second_row_frame, bg='#2d2d2d')
                rpm_frame.pack(side='left', fill='x', expand=True, padx=(0, 5))
                rpm_label_frame = tk.Frame(rpm_frame, bg='#2d2d2d')
                rpm_label_frame.pack(fill='x')
                tk.Label(rpm_label_frame, text="RPM:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                rpm_value = tk.Label(rpm_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                rpm_value.pack(side='right')
                
                # Gear (right side)
                gear_frame = tk.Frame(second_row_frame, bg='#2d2d2d')
                gear_frame.pack(side='right', fill='x', expand=True, padx=(5, 0))
                gear_label_frame = tk.Frame(gear_frame, bg='#2d2d2d')
                gear_label_frame.pack(fill='x')
                tk.Label(gear_label_frame, text="Gear:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                gear_value = tk.Label(gear_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                gear_value.pack(side='right')
                
                # Third row: HMI button (centered)
                third_row_frame = tk.Frame(data_frame, bg='#2d2d2d')
                third_row_frame.pack(fill='x', pady=3)
                
                # HMI button
                hmi_frame = tk.Frame(third_row_frame, bg='#2d2d2d')
                hmi_frame.pack(expand=True)
                hmi_button = HoverButton(
                    hmi_frame,
                    text="HMI",
                    width=6,
                    font=("Segoe UI", 9),
                    bg='#107c10',
                    fg='white',
                    relief="raised",
                    hover_color='green',
                    command=lambda u=unit: self.launch_unit_hmi(u)
                )
                hmi_button.pack()
                
                # Store LFPC widget references
                unit['unit_frame'] = unit_frame
                unit['operations_widgets'] = {
                    'gas_sub_value': gas_sub_value,
                    'load_value': load_value,
                    'rpm_value': rpm_value,
                    'gear_value': gear_value,
                    'hmi_button': hmi_button
                }
                
            else:
                # 230xx units: Env State, RPM, PE Oil Rate, GB Oil Rate, Gas PSI, indicators
                # First row: Env State and RPM side by side
                first_row_frame = tk.Frame(data_frame, bg='#2d2d2d')
                first_row_frame.pack(fill='x', pady=2)
                
                # Env State (left side)
                env_state_frame = tk.Frame(first_row_frame, bg='#2d2d2d')
                env_state_frame.pack(side='left', fill='x', expand=True, padx=(0, 5))
                env_label_frame = tk.Frame(env_state_frame, bg='#2d2d2d')
                env_label_frame.pack(fill='x')
                tk.Label(env_label_frame, text="Env State:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                envolts_value = tk.Label(env_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                envolts_value.pack(side='right')
                
                # RPM (right side)
                rpm_frame = tk.Frame(first_row_frame, bg='#2d2d2d')
                rpm_frame.pack(side='right', fill='x', expand=True, padx=(5, 0))
                rpm_label_frame = tk.Frame(rpm_frame, bg='#2d2d2d')
                rpm_label_frame.pack(fill='x')
                tk.Label(rpm_label_frame, text="RPM:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                rpm_value = tk.Label(rpm_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                rpm_value.pack(side='right')
            
                # Second row: PE Oil Rate and GB Oil Rate side by side
                second_row_frame = tk.Frame(data_frame, bg='#2d2d2d')
                second_row_frame.pack(fill='x', pady=2)
            
                # PE Oil Rate (left side)
                pe_oil_frame = tk.Frame(second_row_frame, bg='#2d2d2d')
                pe_oil_frame.pack(side='left', fill='x', expand=True, padx=(0, 5))
                pe_label_frame = tk.Frame(pe_oil_frame, bg='#2d2d2d')
                pe_label_frame.pack(fill='x')
                tk.Label(pe_label_frame, text="High Rate:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                pe_oil_value = tk.Label(pe_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                pe_oil_value.pack(side='right')
            
                # GB Oil Rate (right side)
                gb_oil_frame = tk.Frame(second_row_frame, bg='#2d2d2d')
                gb_oil_frame.pack(side='right', fill='x', expand=True, padx=(5, 0))
                gb_label_frame = tk.Frame(gb_oil_frame, bg='#2d2d2d')
                gb_label_frame.pack(fill='x')
                tk.Label(gb_label_frame, text="Low Rate:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                gb_oil_value = tk.Label(gb_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                gb_oil_value.pack(side='right')
            
                # Third row: Gas PSI and Gear side by side
                third_row_frame = tk.Frame(data_frame, bg='#2d2d2d')
                third_row_frame.pack(fill='x', pady=2)
            
                # Gas PSI (left side)
                gas_psi_frame = tk.Frame(third_row_frame, bg='#2d2d2d')
                gas_psi_frame.pack(side='left', fill='x', expand=True, padx=(0, 5))
                gas_label_frame = tk.Frame(gas_psi_frame, bg='#2d2d2d')
                gas_label_frame.pack(fill='x')
                tk.Label(gas_label_frame, text="Gas PSI:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                gas_psi_value = tk.Label(gas_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                gas_psi_value.pack(side='right')
                
                # Gear (right side)
                gear_frame = tk.Frame(third_row_frame, bg='#2d2d2d')
                gear_frame.pack(side='right', fill='x', expand=True, padx=(5, 0))
                gear_label_frame = tk.Frame(gear_frame, bg='#2d2d2d')
                gear_label_frame.pack(fill='x')
                tk.Label(gear_label_frame, text="Gear:", font=("Segoe UI", 9), bg='#2d2d2d', fg='white').pack(side='left')
                gear_value = tk.Label(gear_label_frame, text="---", font=("Segoe UI", 10, "bold"), bg='#1a1a1a', fg='#00ff00', relief='sunken', bd=1, width=6)
                gear_value.pack(side='right')
                
                # Indicators frame
                indicators_frame = tk.Frame(data_frame, bg='#2d2d2d')
                indicators_frame.pack(fill='x', pady=3)
                
                # HMI button (left side)
                hmi_button = HoverButton(
                    indicators_frame,
                    text="HMI",
                    width=6,
                    font=("Segoe UI", 9),
                    bg='#107c10',
                    fg='white',
                    relief="raised",
                    hover_color='green',
                    command=lambda u=unit: self.launch_unit_hmi(u)
                )
                hmi_button.pack(side='left', padx=5)
                
                # Create indicator lights for V1, V2, GLT
                v1_indicator = tk.Label(indicators_frame, text="●", font=("Segoe UI", 12, "bold"), bg='#2d2d2d', fg='gray')
                v1_indicator.pack(side='left', padx=2)
                tk.Label(indicators_frame, text="V1", font=("Segoe UI", 8), bg='#2d2d2d', fg='white').pack(side='left', padx=(0, 5))
                
                v2_indicator = tk.Label(indicators_frame, text="●", font=("Segoe UI", 12, "bold"), bg='#2d2d2d', fg='gray')
                v2_indicator.pack(side='left', padx=2)
                tk.Label(indicators_frame, text="V2", font=("Segoe UI", 8), bg='#2d2d2d', fg='white').pack(side='left', padx=(0, 5))
                
                glt_indicator = tk.Label(indicators_frame, text="●", font=("Segoe UI", 12, "bold"), bg='#2d2d2d', fg='gray')
                glt_indicator.pack(side='left', padx=2)
                tk.Label(indicators_frame, text="GLT", font=("Segoe UI", 8), bg='#2d2d2d', fg='white').pack(side='left')
                
                # Store 230xx widget references
                unit['unit_frame'] = unit_frame  # Store unit frame for background flashing
                unit['operations_widgets'] = {
                    'rpm_value': rpm_value,
                    'envolts_value': envolts_value,
                    'pe_oil_value': pe_oil_value,
                    'gb_oil_value': gb_oil_value,
                    'gas_psi_value': gas_psi_value,
                    'gear_value': gear_value,
                    'hmi_button': hmi_button,
                    'v1_indicator': v1_indicator,
                    'v2_indicator': v2_indicator,
                    'glt_indicator': glt_indicator
                }

    def start_operations_monitoring(self):
        """Start monitoring operations data for all units"""
        if self.monitoring_active:
            return
            
        self.monitoring_active = True
        self.start_button.config(text="Monitoring...", bg="#25902a")
        
        # Create and start monitoring threads for each unit
        for unit in self.units_info:
            thread = threading.Thread(target=self.monitor_operations_unit, args=(unit,), daemon=True)
            thread.start()
            self.monitor_threads.append(thread)

    def monitor_operations_unit(self, unit):
        """Monitor operations data for a single unit"""
        ip_address = unit['ip_address']
        widgets = unit.get('operations_widgets', {})
        is_lfpc = unit.get('unit_type') == 'LFPC'
        
        while self.monitoring_active:
            try:
                client = ModbusTcpClient(ip_address)
                if client.connect():
                    if is_lfpc:
                        # LFPC unit monitoring
                        has_red_params = False  # Track if any parameter is red (excluding gear)
                        
                        # Read Gear first to determine gas sub color logic
                        gear_result = client.read_holding_registers(address=270, count=1)
                        gear_display = "N"  # Default
                        if not gear_result.isError():
                            gear_value = gear_result.registers[0]
                            # Display "N" if gear is not 1-9, otherwise display the gear number
                            gear_display = str(gear_value) if 1 <= gear_value <= 9 else "N"
                            # Set gear color: red for "N", white for valid gear numbers
                            gear_color = '#ff0000' if gear_display == "N" else 'white'
                            self.safe_widget_update(widgets.get('gear_value'), text=gear_display, fg=gear_color)
                        
                        # Read Gas Sub % (400250 -> 250)
                        gas_sub_result = client.read_holding_registers(address=250, count=1)
                        if not gas_sub_result.isError():
                            gas_sub_value = gas_sub_result.registers[0]
                            # Color logic: red if gear is not "N" and gas sub is 0%, otherwise green
                            if gear_display != "N" and gas_sub_value == 0:
                                gas_sub_color = '#ff0000'  # Red
                                has_red_params = True
                            else:
                                gas_sub_color = '#00ff00'  # Green
                            self.safe_widget_update(widgets.get('gas_sub_value'), text=f"{gas_sub_value}%", fg=gas_sub_color)
                        
                        # Read Load % (400373 -> 373)
                        load_result = client.read_holding_registers(address=373, count=1)
                        if not load_result.isError():
                            load_value = load_result.registers[0]
                            self.safe_widget_update(widgets.get('load_value'), text=f"{load_value}%")
                        
                        # Read RPM (400370 -> 370)
                        rpm_result = client.read_holding_registers(address=370, count=1)
                        if not rpm_result.isError():
                            rpm_value = rpm_result.registers[0]
                            rpm_color = '#ff0000' if rpm_value == 0 else '#00ff00'  # Red if 0, green otherwise
                            if rpm_value == 0:
                                has_red_params = True
                            self.safe_widget_update(widgets.get('rpm_value'), text=str(rpm_value), fg=rpm_color)
                        
                        # Flash background if any parameter is red (excluding gear)
                        unit_frame = unit.get('unit_frame')
                        if has_red_params and unit_frame:
                            # Alternate background between bright red and normal
                            unit['bg_flash_state'] = not unit.get('bg_flash_state', False)
                            if unit['bg_flash_state']:
                                self.safe_widget_update(unit_frame, bg='#ff0000')
                            else:
                                self.safe_widget_update(unit_frame, bg='#2d2d2d')
                        else:
                            # Reset background to normal when no red parameters
                            if unit_frame:
                                self.safe_widget_update(unit_frame, bg='#2d2d2d')
                    
                    else:
                        # 230xx unit monitoring
                        has_red_params = False  # Track if any parameter is red (excluding gear)
                        
                        # Read Engine RPM (400370 -> 370)
                        rpm_result = client.read_holding_registers(address=370, count=1)
                        if not rpm_result.isError():
                            rpm_value = rpm_result.registers[0]
                            rpm_color = '#ff0000' if rpm_value < 1200 else '#00ff00'  # Red if under 1200, green otherwise
                            if rpm_value < 1200:
                                has_red_params = True
                            self.safe_widget_update(widgets.get('rpm_value'), text=str(rpm_value), fg=rpm_color)
                    
                        # Read Envolts State (302044 -> 2044)
                        envolts_result = client.read_input_registers(address=2044, count=1)
                        if not envolts_result.isError():
                            envolts_value = envolts_result.registers[0]
                            envolts_color = '#00ff00' if envolts_value == 5 else '#ff0000'  # Green if 5, red otherwise
                            if envolts_value != 5:
                                has_red_params = True
                            self.safe_widget_update(widgets.get('envolts_value'), text=str(envolts_value), fg=envolts_color)
                    
                        # Read PE Oil Rate (400494 -> 494) - 32-bit floating point from 2 registers
                        pe_oil_result = client.read_holding_registers(address=494, count=2)
                        if not pe_oil_result.isError():
                            # Combine two 16-bit registers into a 32-bit value and convert to float
                            import struct
                            combined_value = (pe_oil_result.registers[0] << 16) | pe_oil_result.registers[1]
                            pe_oil_value = struct.unpack('>f', struct.pack('>I', combined_value))[0]
                            pe_oil_color = '#ff0000' if pe_oil_value < 34 else '#00ff00'  # Red if less than 34, green otherwise
                            if pe_oil_value < 34:
                                has_red_params = True
                            self.safe_widget_update(widgets.get('pe_oil_value'), text=f"{pe_oil_value:.2f}", fg=pe_oil_color)
                    
                        # Read GB Oil Rate (302033 -> 2033) - 32-bit floating point from 2 registers
                        gb_oil_result = client.read_input_registers(address=2033, count=2)
                        if not gb_oil_result.isError():
                            # Combine two 16-bit registers into a 32-bit value and convert to float
                            import struct
                            combined_value = (gb_oil_result.registers[0] << 16) | gb_oil_result.registers[1]
                            gb_oil_value = struct.unpack('>f', struct.pack('>I', combined_value))[0]
                            gb_oil_color = '#ff0000' if gb_oil_value < 34 else '#00ff00'  # Red if less than 34, green otherwise
                            if gb_oil_value < 34:
                                has_red_params = True
                            self.safe_widget_update(widgets.get('gb_oil_value'), text=f"{gb_oil_value:.2f}", fg=gb_oil_color)
                    
                        # Read Gas PSI (302035 -> 2035)
                        gas_psi_result = client.read_input_registers(address=2035, count=1)
                        if not gas_psi_result.isError():
                            gas_psi_value = gas_psi_result.registers[0]
                            # Gas PSI color logic: below 85 = flashing red, below 100 = flashing amber, otherwise green
                            if gas_psi_value < 85:
                                # Store flashing red state
                                unit['gas_psi_flash_state'] = getattr(unit, 'gas_psi_flash_state', True)
                                unit['gas_psi_flash_state'] = not unit['gas_psi_flash_state']
                                gas_psi_color = '#ff0000' if unit['gas_psi_flash_state'] else '#800000'  # Flashing red
                                has_red_params = True
                            elif gas_psi_value < 100:
                                # Store flashing amber state
                                unit['gas_psi_flash_state'] = getattr(unit, 'gas_psi_flash_state', True)
                                unit['gas_psi_flash_state'] = not unit['gas_psi_flash_state']
                                gas_psi_color = '#ffaa00' if unit['gas_psi_flash_state'] else '#cc8800'  # Flashing amber
                                has_red_params = True
                            else:
                                gas_psi_color = '#00ff00'  # Green
                            self.safe_widget_update(widgets.get('gas_psi_value'), text=str(gas_psi_value), fg=gas_psi_color)
                        
                        # Flash background if any parameter is red (excluding gear)
                        unit_frame = unit.get('unit_frame')
                        if has_red_params and unit_frame:
                            # Alternate background between bright red and normal
                            unit['bg_flash_state'] = not unit.get('bg_flash_state', False)
                            if unit['bg_flash_state']:
                                self.safe_widget_update(unit_frame, bg='#ff0000')
                            else:
                                self.safe_widget_update(unit_frame, bg='#2d2d2d')
                        else:
                            # Reset background to normal when no red parameters
                            if unit_frame:
                                self.safe_widget_update(unit_frame, bg='#2d2d2d')
                    
                        # Read Gear (400270 -> 270)
                        gear_result = client.read_holding_registers(address=270, count=1)
                        if not gear_result.isError():
                            gear_value = gear_result.registers[0]
                            # Display "N" if gear is not 1-9, otherwise display the gear number
                            gear_display = str(gear_value) if 1 <= gear_value <= 9 else "N"
                            # Set gear color: red for "N", white for valid gear numbers
                            gear_color = '#ff0000' if gear_display == "N" else 'white'
                            self.safe_widget_update(widgets.get('gear_value'), text=gear_display, fg=gear_color)
                    
                        # V1 (302002.05) - bit 5 of register 302002 -> 2002
                        v1_result = client.read_input_registers(address=2002, count=1)
                        if not v1_result.isError():
                            v1_state = bool(v1_result.registers[0] & (1 << 5))
                            color = '#00ff00' if v1_state else 'gray'
                            self.safe_widget_update(widgets.get('v1_indicator'), fg=color)
                        
                        # V2 (302002.06) - bit 6 of register 302002 -> 2002
                        v2_result = client.read_input_registers(address=2002, count=1)
                        if not v2_result.isError():
                            v2_state = bool(v2_result.registers[0] & (1 << 6))
                            color = '#00ff00' if v2_state else 'gray'
                            self.safe_widget_update(widgets.get('v2_indicator'), fg=color)
                        
                        # GLT (302002.07) - bit 7 of register 302002 -> 2002
                        glt_result = client.read_input_registers(address=2002, count=1)
                        if not glt_result.isError():
                            glt_state = bool(glt_result.registers[0] & (1 << 7))
                            color = '#00ff00' if glt_state else 'gray'
                            self.safe_widget_update(widgets.get('glt_indicator'), fg=color)
                    
                    client.close()
                    
            except Exception as e:
                print(f"Error monitoring operations for unit {unit['unit_name']} at {ip_address}: {e}")
                # Update all widgets to show error state
                for widget_name, widget in widgets.items():
                    if 'indicator' in widget_name:
                        self.safe_widget_update(widget, fg='red')
                    else:
                        self.safe_widget_update(widget, text="ERR")
            
            # Wait before next reading
            time.sleep(2)

    def create_controls_page(self):
        """Create the Controls page accessible from maintenance page"""
        if self.current_frame:
            self.current_frame.destroy()

        self.current_frame = tk.Frame(self.root)
        self.current_frame.configure(bg='#1e1e1e')
        self.current_frame.pack(expand=True, fill='both', padx=30, pady=20)

        # Modern header with subtle bottom border
        header_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        header_frame.pack(fill='x', pady=(0, 5))
        
        header_label = tk.Label(
            header_frame,
            text="Controls - Log Download/Reboot & Quick Reboot",
            font=("Segoe UI", 26, "bold"),
            bg='#1e1e1e',
            fg='white'
        )
        header_label.pack(pady=(0, 5))
        
        separator = ttk.Separator(header_frame, orient='horizontal')
        separator.pack(fill='x', padx=50)
        
        # Find only 230xx folders and read their IP addresses (ignore LFPC units)
        self.units_info = self.find_230xx_folders()
        
        if not self.units_info:
            # Create a placeholder frame for consistent layout
            placeholder_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
            placeholder_frame.pack(expand=True, fill='both')
            
            no_units_label = tk.Label(
                placeholder_frame,
                text="No 230xx units found. Please scan for units first.",
                font=("Segoe UI", 16),
                bg='#1e1e1e',
                fg='white'
            )
            no_units_label.pack(expand=True, pady=50)
            
            # Back button
            back_button = HoverButton(
                self.current_frame,
                text="Back to Maintenance",
                width=20,
                font=("Segoe UI", 12, "bold"),
                bg="#0078d4",
                fg="white",
                relief="flat",
                hover_color="#2b88d8",
                command=self.create_maintenance_page
            )
            back_button.pack(pady=20)
            return

        # Create a frame for the units display with modern styling
        self.controls_grid_frame = tk.Frame(self.current_frame, bg='#1e1e1e')
        self.controls_grid_frame.pack(expand=True, fill='both', padx=10, pady=10)
        
        # Create control displays for each unit
        self.create_controls_monitors()
        
        # Modern styled bottom control buttons
        button_frame = tk.Frame(self.current_frame, bg='#1e1e1e', pady=15)
        button_frame.pack(side='bottom', fill='x')
        
        # Back to Maintenance button
        back_button = HoverButton(
            button_frame,
            text="Back to Maintenance",
            width=20,
            font=("Segoe UI", 12, "bold"),
            bg="#0078d4",
            fg="white",
            relief="flat",
            hover_color="#2b88d8",
            command=self.create_maintenance_page
        )
        back_button.pack(side='left', padx=10, ipady=5)

    def create_controls_monitors(self):
        """Create control displays for each unit with download and reboot buttons"""
        # Load pump assignments to map pump numbers to unit numbers
        pump_assignments = self.load_assignments()
        
        # Create a mapping of unit numbers to their assigned pump numbers
        unit_to_pump_map = {}
        for pump_num, data in pump_assignments.items():
            if data.get('exe_name') != 'Select Pump':
                unit_to_pump_map[data.get('exe_name')] = pump_num
        
        # Sort units based on their pump assignments
        sorted_units = []
        unassigned_units = []
        
        for unit in self.units_info:
            unit_name = unit['unit_name']
            if unit_name in unit_to_pump_map.keys():
                # Add pump number to unit info
                unit['pump_number'] = unit_to_pump_map[unit_name]
                sorted_units.append(unit)
            else:
                # Unit not assigned to any pump
                unit['pump_number'] = None
                unassigned_units.append(unit)
        
        # Sort units by pump number
        sorted_units.sort(key=lambda u: int(u['pump_number']))
        
        # Add unassigned units at the end
        all_units = sorted_units + unassigned_units
        
        # Calculate rows and columns (4 rows per column for better layout)
        rows_per_column = 4
        num_units = len(all_units)
        num_columns = (num_units + rows_per_column - 1) // rows_per_column
        
        for i, unit in enumerate(all_units):
            # Calculate position (column first, then row)
            col = i // rows_per_column
            row = i % rows_per_column
            
            # Create a frame for this unit (larger for control buttons)
            unit_frame = tk.Frame(self.controls_grid_frame, bg='#2d2d2d', padx=15, pady=15, bd=2, relief='solid', width=320, height=180)
            unit_frame.grid(row=row, column=col, padx=10, pady=10, sticky='nsew')
            unit_frame.grid_propagate(False)  # Force the frame to maintain its size
            
            # Unit header with name and IP
            header = tk.Frame(unit_frame, bg='#2d2d2d')
            header.pack(fill='x', pady=(0, 10))
            
            # Display format: "Pump # - Unit ###" if pump number exists
            if unit['pump_number'] is not None:
                displayed_pump_num = int(unit['pump_number']) + 1
                label_text = f"Pump {displayed_pump_num} - {unit['unit_name']}"
            else:
                label_text = f"{unit['unit_name']}"
                
            unit_label = tk.Label(
                header,
                text=label_text,
                font=("Segoe UI", 12, "bold"),
                bg='#2d2d2d',
                fg='white'
            )
            unit_label.pack(side='left')
            
            ip_label = tk.Label(
                header,
                text=f"IP: {unit['ip_address']}",
                font=("Segoe UI", 10),
                bg='#2d2d2d',
                fg='#aaaaaa'
            )
            ip_label.pack(side='right')
            
            # Separator
            separator = ttk.Separator(unit_frame, orient='horizontal')
            separator.pack(fill='x', pady=(0, 10))
            
            # Control buttons frame
            buttons_frame = tk.Frame(unit_frame, bg='#2d2d2d')
            buttons_frame.pack(fill='both', expand=True)
            
            # Download Logs button (smaller, side by side)
            download_button = HoverButton(
                buttons_frame,
                text="Download Logs",
                font=("Segoe UI", 9, "bold"),
                bg="#107c10",
                fg="white",
                relief="flat",
                hover_color="#25902a",
                command=lambda u=unit: self.download_unit_logs(u)
            )
            download_button.pack(side='left', fill='both', expand=True, padx=(0, 5), pady=5, ipady=5)
            
            # Reboot Unit button (smaller, side by side)
            reboot_button = HoverButton(
                buttons_frame,
                text="Reboot Unit",
                font=("Segoe UI", 9, "bold"),
                bg="#d83b01",
                fg="white",
                relief="flat",
                hover_color="#e85b24",
                command=lambda u=unit: self.reboot_unit(u)
            )
            reboot_button.pack(side='left', fill='both', expand=True, padx=(5, 0), pady=5, ipady=5)
            
            # Store references for potential future use
            unit['control_widgets'] = {
                'unit_frame': unit_frame,
                'download_button': download_button,
                'reboot_button': reboot_button
            }

    def download_unit_logs(self, unit):
        """Download logs from /c/jobs/ folder via SSH, organize them, and reboot unit"""
        unit_name = unit['unit_name']
        ip_address = unit['ip_address']
        
        # Confirmation dialog
        result = messagebox.askyesno(
            "Confirm Download & Reboot", 
            f"Are you sure you want to download logs from {unit_name} ({ip_address})?\n\nThis will:\n1. Download the 15 most recent files from /c/jobs/\n2. Delete ALL files from /c/jobs/ folder\n3. Reboot the unit",
            icon='question'
        )
        
        if not result:
            return
        
        # Show progress dialog
        progress_window = tk.Toplevel(self.root)
        progress_window.title(f"Downloading Logs - {unit_name}")
        progress_window.geometry("400x150")
        progress_window.configure(bg='#1e1e1e')
        progress_window.transient(self.root)
        progress_window.grab_set()
        
        # Center the progress window
        progress_window.geometry("+%d+%d" % (self.root.winfo_rootx() + 50, self.root.winfo_rooty() + 50))
        
        progress_label = tk.Label(
            progress_window,
            text=f"Connecting to {unit_name} ({ip_address})...",
            font=("Segoe UI", 12),
            bg='#1e1e1e',
            fg='white'
        )
        progress_label.pack(pady=20)
        
        progress_bar = ttk.Progressbar(progress_window, length=300, mode='indeterminate')
        progress_bar.pack(pady=10)
        progress_bar.start()
        
        def download_task():
            try:
                # SSH connection parameters
                ssh_username = "admin"
                ssh_password = "LBRT123!"
                remote_path = "/c/jobs/"
                
                # Create SSH client
                ssh = paramiko.SSHClient()
                ssh.set_missing_host_key_policy(paramiko.AutoAddPolicy())
                
                # Update progress
                self.root.after(0, lambda: progress_label.config(text="Establishing SSH connection..."))
                
                # Connect to the unit
                ssh.connect(ip_address, username=ssh_username, password=ssh_password, timeout=30)
                
                # Create SFTP client
                sftp = ssh.open_sftp()
                
                # Update progress
                self.root.after(0, lambda: progress_label.config(text="Checking remote directory..."))
                
                # Check if remote directory exists and get file list with timestamps
                try:
                    file_list = sftp.listdir_attr(remote_path)
                    if not file_list:
                        self.root.after(0, lambda: self.show_message("Info", f"No files found in {remote_path} on {unit_name}"))
                        return
                except FileNotFoundError:
                    self.root.after(0, lambda: self.show_message("Error", f"Directory {remote_path} not found on {unit_name}"))
                    return
                
                # Sort files by modification time (most recent first) and get top 15
                file_list.sort(key=lambda x: x.st_mtime, reverse=True)
                files_to_download = file_list[:15]  # Get 15 most recent files
                all_filenames = [f.filename for f in file_list]  # All files for deletion
                
                # Create local directory structure
                logs_dir = os.path.join("C:", "Logs")
                unit_dir = os.path.join(logs_dir, unit_name)
                
                # Create datetime folder
                now = datetime.now()
                datetime_folder = now.strftime("%Y-%m-%d_%H-%M-%S")
                download_dir = os.path.join(unit_dir, datetime_folder)
                
                os.makedirs(download_dir, exist_ok=True)
                
                # Update progress
                total_files = len(file_list)
                files_to_download_count = len(files_to_download)
                self.root.after(0, lambda: progress_label.config(text=f"Downloading {files_to_download_count} most recent files (of {total_files} total)..."))
                
                # Download the 15 most recent files
                downloaded_files = []
                for file_attr in files_to_download:
                    filename = file_attr.filename
                    remote_file_path = remote_path + filename
                    local_file_path = os.path.join(download_dir, filename)
                    
                    try:
                        sftp.get(remote_file_path, local_file_path)
                        downloaded_files.append(filename)
                    except Exception as e:
                        print(f"Error downloading {filename}: {e}")
                
                # Update progress
                self.root.after(0, lambda: progress_label.config(text=f"Deleting ALL {total_files} files from jobs folder..."))
                
                # Delete ALL files from remote directory (not just downloaded ones)
                deleted_files = []
                for filename in all_filenames:
                    try:
                        remote_file_path = remote_path + filename
                        sftp.remove(remote_file_path)
                        deleted_files.append(filename)
                    except Exception as e:
                        print(f"Error deleting remote file {filename}: {e}")
                
                # Verify remote directory is empty
                try:
                    remaining_files = sftp.listdir(remote_path)
                except:
                    remaining_files = []
                
                # Close connections
                sftp.close()
                ssh.close()
                
                # Always proceed with reboot after clearing jobs folder
                self.root.after(0, lambda: progress_label.config(text="Jobs folder cleared. Rebooting unit..."))
                
                # Reconnect for reboot (previous connection was closed)
                ssh_reboot = paramiko.SSHClient()
                ssh_reboot.set_missing_host_key_policy(paramiko.AutoAddPolicy())
                ssh_reboot.connect(ip_address, username=ssh_username, password=ssh_password, timeout=30)
                
                # Execute reboot command
                stdin, stdout, stderr = ssh_reboot.exec_command("sudo reboot")
                ssh_reboot.close()
                
                # Create completion message
                if remaining_files:
                    message = f"Downloaded {len(downloaded_files)} most recent files to:\n{download_dir}\n\nDeleted {len(deleted_files)} files from jobs folder.\nWarning: {len(remaining_files)} files could not be deleted.\nReboot command sent to {unit_name}."
                else:
                    message = f"Downloaded {len(downloaded_files)} most recent files to:\n{download_dir}\n\nDeleted all {len(deleted_files)} files from jobs folder.\nReboot command sent to {unit_name}."
                
                self.root.after(0, lambda: self.show_message("Success", message))
                
            except paramiko.AuthenticationException:
                self.root.after(0, lambda: self.show_message("Error", f"Authentication failed for {unit_name}. Check SSH credentials."))
            except paramiko.SSHException as e:
                self.root.after(0, lambda: self.show_message("Error", f"SSH connection error for {unit_name}: {str(e)}"))
            except Exception as e:
                self.root.after(0, lambda: self.show_message("Error", f"Error downloading logs from {unit_name}: {str(e)}"))
            finally:
                self.root.after(0, lambda: progress_window.destroy())
        
        # Start download in separate thread
        threading.Thread(target=download_task, daemon=True).start()

    def reboot_unit(self, unit):
        """Quick reboot the unit via SSH without checking files"""
        unit_name = unit['unit_name']
        ip_address = unit['ip_address']
        
        # Confirmation dialog
        result = messagebox.askyesno(
            "Confirm Quick Reboot", 
            f"Are you sure you want to reboot {unit_name} ({ip_address})?\n\nThis will:\n1. Immediately send 'sudo reboot' command\n2. Disconnect the unit\n\nNote: This is a quick reboot and does not check for files.",
            icon='warning'
        )
        
        if not result:
            return
        
        # Show progress dialog
        progress_window = tk.Toplevel(self.root)
        progress_window.title(f"Quick Rebooting - {unit_name}")
        progress_window.geometry("400x150")
        progress_window.configure(bg='#1e1e1e')
        progress_window.transient(self.root)
        progress_window.grab_set()
        
        # Center the progress window
        progress_window.geometry("+%d+%d" % (self.root.winfo_rootx() + 50, self.root.winfo_rooty() + 50))
        
        progress_label = tk.Label(
            progress_window,
            text=f"Connecting to {unit_name} ({ip_address})...",
            font=("Segoe UI", 12),
            bg='#1e1e1e',
            fg='white'
        )
        progress_label.pack(pady=20)
        
        progress_bar = ttk.Progressbar(progress_window, length=300, mode='indeterminate')
        progress_bar.pack(pady=10)
        progress_bar.start()
        
        def reboot_task():
            try:
                # SSH connection parameters
                ssh_username = "admin"
                ssh_password = "LBRT123!"
                
                # Create SSH client
                ssh = paramiko.SSHClient()
                ssh.set_missing_host_key_policy(paramiko.AutoAddPolicy())
                
                # Update progress
                self.root.after(0, lambda: progress_label.config(text="Establishing SSH connection..."))
                
                # Connect to the unit
                ssh.connect(ip_address, username=ssh_username, password=ssh_password, timeout=30)
                
                # Update progress
                self.root.after(0, lambda: progress_label.config(text="Sending reboot command..."))
                
                # Execute reboot command immediately
                stdin, stdout, stderr = ssh.exec_command("sudo reboot")
                
                # Close SSH connection (it will be terminated by reboot anyway)
                ssh.close()
                
                # Show completion message
                self.root.after(0, lambda: self.show_message("Success", f"Quick reboot command sent to {unit_name}.\nThe unit should restart shortly."))
                
            except paramiko.AuthenticationException:
                self.root.after(0, lambda: self.show_message("Error", f"Authentication failed for {unit_name}. Check SSH credentials."))
            except paramiko.SSHException as e:
                self.root.after(0, lambda: self.show_message("Error", f"SSH connection error for {unit_name}: {str(e)}"))
            except Exception as e:
                self.root.after(0, lambda: self.show_message("Error", f"Error rebooting {unit_name}: {str(e)}"))
            finally:
                self.root.after(0, lambda: progress_window.destroy())
        
        # Start reboot in separate thread
        threading.Thread(target=reboot_task, daemon=True).start()

    def show_message(self, title, message):
        """Helper method to show message boxes from threads"""
        if title == "Success":
            messagebox.showinfo(title, message)
        elif title == "Warning" or title == "Info":
            messagebox.showwarning(title, message)
        else:
            messagebox.showerror(title, message)

    def load_existing_configuration(self):
        # Reset monitoring state tracking when navigating to main page
        self.was_monitoring_before_navigation = False
        
        # Stop any active monitoring before navigation
        if self.monitoring_active:
            self.stop_monitoring()
        
        # Deactivate auto fan when navigating away from monitor page
        if self.auto_control_active:
            print("Deactivating auto fan control due to navigation")
            self.auto_control_active = False
            
        try:
            if os.path.exists('pump_assignments.json'):
                with open('pump_assignments.json', 'r') as f:
                    assignments = json.load(f)
                    if assignments:
                        # Get the number of pumps from the existing assignments
                        num_pumps = max([int(k) for k in assignments.keys()]) + 1
                        # Store the assignments before creating the main page
                        self.pump_assignments = {int(k): {"exe_name": v["exe_name"]}
                                              for k, v in assignments.items()}
                        # Create the main page with the existing number of pumps
                        self.create_main_page(num_pumps)
                    else:
                        messagebox.showwarning("No Configuration",
                                             "No existing pump configuration found. Please use 'New Pumps or New Site'.")
            else:
                messagebox.showwarning("No Configuration",
                                     "No existing pump configuration found. Please use 'New Pumps or New Site'.")
        except Exception as e:
            messagebox.showerror("Error", f"Error loading configuration: {e}")


if __name__ == "__main__":
    root = tk.Tk()
    app = ModernApp(root)
    root.mainloop()