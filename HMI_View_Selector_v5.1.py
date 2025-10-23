#!/usr/bin/env python3
"""
HMI View Selector v5.1
Industrial Control System Management Software
Copyright (c) 2025
Licensed under MIT License

This is a legitimate industrial automation software for managing HMI interfaces.
It provides a secure way to manage and switch between different pump control interfaces.
"""

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
from concurrent.futures import ThreadPoolExecutor
from pymodbus.client import ModbusTcpClient

# Software version and metadata
__version__ = "5.1"
__author__ = "Industrial Control Systems"
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
        self.config(bg=self.hover_color)

    def on_leave(self, e):
        self.config(bg=self.default_color)


class ModernApp:
    def __init__(self, root):
        self.pump_input = None
        self.root = root
        self.root.title("HMI View Selector v5.1")
        self.root.configure(bg='#1e1e1e')  # Dark modern background

        # Initialize variables
        self.exe_folder = "Digi_Prime_HMIs"
        self.exe_files = self.get_exe_files()
        self.current_frame = None
        self.pump_assignments = self.load_assignments()
        self.monitoring_active = False
        self.auto_control_active = False
        self.auto_threshold = 1047  # Temperature threshold for auto-control
        self.monitor_threads = []
        self.units_info = []
        
        # IP range configuration - default values
        self.ip_start = [10, 55, 10, 100]
        self.ip_end = [10, 55, 10, 255]
        self.load_ip_config()

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
            command=self.create_ip_setup_page,
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
            command=self.create_ip_setup_page,
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
            command=self.create_ini_page,
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
            
            for i, entry in enumerate(self.start_ip_entries):
                value = int(entry.get())
                if not (0 <= value <= 255):
                    messagebox.showerror("Invalid Input", f"Start IP octet {i+1} must be between 0 and 255")
                    return
                start_ip.append(value)
            
            for i, entry in enumerate(self.end_ip_entries):
                value = int(entry.get())
                if not (0 <= value <= 255):
                    messagebox.showerror("Invalid Input", f"End IP octet {i+1} must be between 0 and 255")
                    return
                end_ip.append(value)
            
            # Validate that start IP is less than or equal to end IP
            start_ip_int = (start_ip[0] << 24) + (start_ip[1] << 16) + (start_ip[2] << 8) + start_ip[3]
            end_ip_int = (end_ip[0] << 24) + (end_ip[1] << 16) + (end_ip[2] << 8) + end_ip[3]
            
            if start_ip_int > end_ip_int:
                messagebox.showerror("Invalid Range", "Start IP must be less than or equal to End IP")
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
        
        # Find 230xx folders and read their IP addresses
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
        
        # Auto control button
        self.auto_button = HoverButton(
            button_frame,
            text="Auto Fan OFF",
            width=15,
            font=("Segoe UI", 12, "bold"),
            bg="#0078d4",  # Blue when inactive
            fg="white",
            relief="flat",
            hover_color="#2b88d8",  # Lighter blue on hover
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
            
            # Create a frame for this unit (50% smaller)
            unit_frame = tk.Frame(self.grid_frame, bg='#2d2d2d', padx=7, pady=7, bd=1, relief='solid', width=175, height=150)
            unit_frame.grid(row=row, column=col, padx=5, pady=5, sticky='nsew')
            unit_frame.grid_propagate(False)  # Force the frame to maintain its size
            
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
            
            # Status indicators frame
            indicators_frame = tk.Frame(unit_frame, bg='#2d2d2d')
            indicators_frame.pack(fill='x', pady=2)
            
            # Turbo Temp display
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
            
            # Digital display for Turbo Temp
            turbo_value = tk.Label(
                turbo_frame,
                text="---",
                font=("Segoe UI", 9, "bold"),
                width=4,
                bg='#1e1e1e',
                fg='#00ff00',
                relief='sunken',
                bd=1
            )
            turbo_value.pack(side='left', padx=5)
            
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
                font=("Segoe UI", 9, "bold"),
                width=4,
                bg='#1e1e1e',
                fg='#00ff00',
                relief='sunken',
                bd=1
            )
            battery_value.pack(side='left', padx=5)
            
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
                bd=1
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
                text="Send",
                width=4,
                font=("Segoe UI", 9),
                bg='#0078d4',
                fg='white',
                relief="raised",
                hover_color='#2b88d8',
                command=lambda u=unit, v=input_var: self.send_register_value(u, v, 1212)
            )
            send_button.pack(side='left', padx=2)
            
            # Combined status indicator (including PLC status)
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
            
            # Indicator light
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
            
            # Remove fan indicator - no longer needed
            
            # Button container frame for control and HMI buttons
            buttons_frame = tk.Frame(indicators_frame, bg='#2d2d2d')
            buttons_frame.pack(side='right', padx=5)
            
            # Control button for register 401000
            control_button = HoverButton(
                buttons_frame,
                text="fan",
                width=4,
                font=("Segoe UI", 9),
                bg='#0078d4',  # Default blue color
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
                hover_color='#0ea10e',
                command=lambda u=unit: self.launch_unit_hmi(u)
            )
            hmi_button.pack(side='right', padx=2)
            
            # Store the widgets in the unit info for updates
            unit['widgets'] = {
                'turbo_value': turbo_value,
                'battery_value': battery_value,
                'setpoint_value': setpoint_value,
                'status_light': status_light,
                'control_button': control_button,
                'hmi_button': hmi_button,
                'input_var': input_var,
                'value_entry': value_entry,
                'flash_state': False  # For controlling indicator flashing
            }
    
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
                thread.join(0.5)  # Wait longer (500ms) for each thread to terminate
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
        print(f"Starting monitoring thread for unit {unit_name} at {ip}")
        
        try:
            widgets = unit['widgets']
            flash_counter = 0
            
            while self.monitoring_active:
                # Exit if monitoring has been deactivated
                if not self.monitoring_active:
                    print(f"Monitoring deactivated for unit {unit_name}, exiting thread")
                    break
                
                client = ModbusTcpClient(ip)  # Create new client each iteration for better error handling
                
                try:
                    if client.connect():
                        # Read Turbo Temp (address: 302075)
                        turbo_result = client.read_input_registers(address=2075, count=1)
                        if not turbo_result.isError():
                            turbo_temp = turbo_result.registers[0]
                            self.root.after(0, lambda w=widgets['turbo_value'], v=turbo_temp: w.config(text=f"{v}"))
                        
                        # Read Battery % (address: 302027)
                        battery_result = client.read_input_registers(address=2027, count=1)
                        if not battery_result.isError():
                            battery_value = battery_result.registers[0]
                            
                            # Check if battery is low (below 50%)
                            if battery_value < 50:
                                # Flash red for low battery warning
                                flash_counter = (flash_counter + 1) % 4
                                if flash_counter < 2:  # Alternate every 2 cycles
                                    # Red text on dark background for warning
                                    self.root.after(0, lambda w=widgets['battery_value'], v=battery_value: 
                                                   w.config(text=f"{v}", fg="red", font=("Segoe UI", 11, "bold")))
                                else:
                                    # Normal text
                                    self.root.after(0, lambda w=widgets['battery_value'], v=battery_value: 
                                                   w.config(text=f"{v}", fg="white", font=("Segoe UI", 11)))
                            else:
                                # Normal display for healthy battery
                                self.root.after(0, lambda w=widgets['battery_value'], v=battery_value: 
                                               w.config(text=f"{v}", fg="white", font=("Segoe UI", 11)))
                            
                        # Read current value from register 401212
                        setting_result = client.read_holding_registers(address=1212, count=1)
                        if not setting_result.isError():
                            current_setting = setting_result.registers[0]
                            # Update the setpoint display with current value
                            self.root.after(0, lambda w=widgets['setpoint_value'], v=current_setting: w.config(text=f"{v}"))
                            
                            # Check for auto-control trigger condition - activate fan if turbo temp >= 1047
                            if self.auto_control_active and turbo_temp >= 1047:
                                print(f"Auto-control triggered: Fan activation for {unit_name} - Turbo temp: {turbo_temp}")
                                # Trigger the fan button (send 100 to register 401000)
                                register_address = 1000 # Address for 401000
                                
                                # Always send 100 to register 401000 when temp threshold is reached
                                fan_result = client.write_register(address=register_address, value=100)
                                if not fan_result.isError():
                                    print(f"Successfully activated fan for {unit_name} due to high temperature ({turbo_temp})")
                                else:
                                    print(f"Error activating fan for {unit_name}: {fan_result}")
                        
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
                                self.root.after(0, lambda w=widgets['status_light']: w.config(bg='red'))
                            else:
                                self.root.after(0, lambda w=widgets['status_light']: w.config(bg='green'))
                        else:
                            # No issues - show steady green
                            self.root.after(0, lambda w=widgets['status_light']: w.config(bg='green'))

                        # Read control value from holding register 401000 (address 1000)
                        response = client.read_holding_registers(address=1000, count=1)
                        if not response.isError():
                            control_value = response.registers[0]
                            # For register 401000: value 100 = ON, make fan button flash red
                            if control_value == 100:
                                # Flash the fan button red when 401000 = 100
                                flash_counter = (flash_counter + 1) % 4
                                if flash_counter < 2:  # Alternate every 2 cycles
                                    self.root.after(0, lambda w=widgets['control_button']: w.config(bg='red'))
                                else:
                                    self.root.after(0, lambda w=widgets['control_button']: w.config(bg='#d83b01'))  # Darker red
                            else:
                                # Normal blue color when 401000 = 0
                                self.root.after(0, lambda w=widgets['control_button']: w.config(bg='#0078d4'))
                except Exception as e:
                    print(f"Error in monitor loop for {unit_name}: {e}")
                    # Reset displays on error
                    self.root.after(0, lambda w=widgets['turbo_value']: w.config(text="---"))
                    self.root.after(0, lambda w=widgets['battery_value']: w.config(text="---"))
                    self.root.after(0, lambda w=widgets['setpoint_value']: w.config(text="---"))
                    self.root.after(0, lambda w=widgets['status_light']: w.config(bg='gray'))
                    # Reset fan button color on error
                    self.root.after(0, lambda w=widgets['control_button']: w.config(bg='#0078d4'))
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
                    
                # Sleep between polling cycles - 500ms update rate
                time.sleep(0.5)  # Exactly 500ms

        except Exception as e:
            print(f"Error in monitor thread for {unit['unit_name']}: {e}")

    
    def toggle_auto_control(self):
        """Toggle the auto control feature"""
        self.auto_control_active = not self.auto_control_active
        
        if self.auto_control_active:
            # Change button appearance to indicate active state
            self.auto_button.config(text="Auto Fan ON", bg="#d83b01")  # Red when active
            
            # Auto-start monitoring if not already running
            if not self.monitoring_active:
                self.start_monitoring()
        else:
            # Reset to inactive appearance
            self.auto_button.config(text="Auto Fan OFF", bg="#0078d4")  # Blue when inactive
    
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
                print(f"Error: Value must be a number (received '{value_str}')")
                return
                
            value = int(value_str)
            if value < 0 or value > 100:
                print(f"Error: Value must be between 0-100 (received {value})")
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
            
    def load_existing_configuration(self):
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